#pragma once
#include<iostream>
#include<fstream>
#include<boost/multiprecision/cpp_int.hpp>
#include<nlohmann/json.hpp>
#include<vector>
#include<blst.h>
#include<unordered_map>
#define G1_SIZE 96 
#define G2_SIZE 192
using std::vector,std::string,std::unordered_map;
using namespace boost::multiprecision;
using json= nlohmann::json;
blst_scalar modular_exp(const blst_scalar& b, size_t e) {
    if(e == 1) return b;
    uint64_t temp[4]={1,0,0,0};
    blst_scalar d,base=b;
    blst_scalar_from_uint64(&d,temp);
    while(e > 0){
        if( e & 1) blst_sk_mul_n_check(&d,&d,&base);
        blst_sk_mul_n_check(&base,&base,&base);
        e = e >> 1;
    }    
    return d;
}

std::ostream&  operator <<(std::ostream& Cout,const blst_scalar& s) { //print blst_scalar in hex
    byte out[32];
    blst_bendian_from_scalar(out,&s);
    for(unsigned i=0;i<32;i++) {
        Cout<<std::hex<<std::setw(2)<<std::setfill('0')<<(int)out[i];
    }
    return Cout;
}
//polynomial operation stuffs
namespace Polynomial{
    using polynomial = std::vector<blst_scalar>;
    std::ostream& operator <<(std::ostream& COUT,polynomial& a) {
        COUT<<"{ ";
        for(auto &x:a) COUT<<x<<" ,";
        COUT<<"}";
        return COUT;
    }
    //NTT algorithm for multiplication
    //evalaute at sub-field of order k
    BOOST_MATH_GPU_ENABLED polynomial NTT(const blst_scalar& omega, size_t k,polynomial&poly) {
        static auto bit_reverse=[](size_t bit,size_t idx) {
            size_t result=0;
            while(bit--){
                result = (result << 1) | (idx & 1);
                idx = idx >> 1;
            }
            return result;
        };
        size_t bits=log2(k);
        uint64_t z[4]={0,0,0,0};
        blst_scalar zero;
        blst_scalar_from_uint64(&zero,z);
        polynomial result(k);
        for(size_t i=0;i<k;i++) {
            size_t idx= bit_reverse(bits,i);
            result[i]= (idx < poly.size()) ? poly[idx]:zero;
        }
        size_t stride=1,power=k/2;
        z[0]=1;
        blst_scalar om,temp,a,b;
        while(stride < k) {
            for(size_t start=0;start< k;start+=stride*2) {
                size_t end= start + stride;
                blst_scalar_from_uint64(&om,z);
                for(size_t i=start; i< end;i++) {
                    temp= modular_exp(om,power);
                    a=result[i];
                    blst_sk_mul_n_check(&b,&result[i+stride],&temp);
                    blst_sk_add_n_check(&result[i],&a,&b);
                    blst_sk_sub_n_check(&result[i+stride],&a,&b);
                    blst_sk_mul_n_check(&om,&omega,&om);
                }
            }
            stride = stride << 1;
            power = power >> 1;
        }
        return result;
    }

    //perform inverseNTT and return the polynomial of degree degree.
    BOOST_MATH_GPU_ENABLED polynomial invNTT(const blst_scalar&omega,size_t k, polynomial&poly) {
        auto result=NTT(omega,k,poly);
        uint64_t z[4]={k,0,0,0};
        blst_scalar zero;
        blst_scalar_from_uint64(&zero,z);
        blst_scalar inv;
        blst_sk_inverse(&inv,&zero);
        blst_sk_mul_n_check(&result[0],&result[0],&inv);
        blst_sk_mul_n_check(&result[k/2],&result[k/2],&inv);
        for(size_t i=1;i<k/2;i++) {
            blst_sk_mul_n_check(&result[i],&result[i],&inv);
            blst_sk_mul_n_check(&result[k-i],&result[k-i],&inv);
            std::swap(result[i],result[k-i]);
        }
        return result;
    }
    
    BOOST_MATH_GPU_ENABLED polynomial poly_multiply(const blst_scalar& omega,size_t k, polynomial&a, polynomial&b) {
        polynomial a_eval= NTT(omega,k,a) , b_eval=NTT(omega,k,b);
        polynomial result(k);
        for(size_t i=0;i<k;i++) blst_sk_mul_n_check(&result[i],&a_eval[i],&b_eval[i]);
        return invNTT(omega,k,result);
    }
    //division: hardcoded for cyclotomic polynomial only: n as a cyclotomic polynomial of form x^n -1.
    BOOST_MATH_GPU_ENABLED polynomial poly_divide(const polynomial& poly,size_t n) {
        blst_scalar zero;
        std::memset(zero.b,0x00,32);
        //n-th cyclotomic polynomial
        size_t m=poly.size()-1;
        size_t k=  m- n;
        vector<blst_scalar>h(k+1,zero),remainder=poly;
        do{
            blst_sk_add_n_check(&h[k],&h[k],&remainder[n+k]);
            blst_sk_sub_n_check(&remainder[n+k],&remainder[n+k],&h[k]);
            blst_sk_add_n_check(&remainder[k],&remainder[k],&h[k]); //x^n-1 is our divisor 
        }while(k--);
        //internal checking that remainder must be zero:
        for(auto& x:remainder) {
            if(blst_sk_check(&x)){ //return true if non-zero
                std::cerr<<"Encounter non-zero in remainder:"<<x<<std::endl;
                exit(1);
            }
        }
        return h;
    }

    polynomial poly_add(polynomial & a, polynomial &b) { 
        size_t n=a.size(),m=b.size();
        polynomial result;
        if(n >= m){
            result.assign(a.begin(),a.end());
            for(size_t i=0;i<m;i++) blst_sk_add_n_check(&result[i],&result[i],&b[i]);

        }
        else{
            result.assign(b.begin(),b.end());
            for(size_t i=0;i<n;i++) blst_sk_add_n_check(&result[i],&result[i],&a[i]);
        }
        return result;
    }
    polynomial operator +(polynomial&a,polynomial& b) {
        return poly_add(a,b);
    }
    polynomial poly_subtract(polynomial& a, polynomial& b) {
        polynomial result(a.begin(),a.end());
        for(size_t i=0;i<b.size();i++) blst_sk_sub_n_check(&result[i],&result[i],&b[i]);
        return result;
    }
    void poly_scalar_mul(polynomial& a, blst_scalar& b){
        for(auto &x:a) blst_sk_mul_n_check(&x,&x,&b);
    }
     //evaluate the polynomial at a given value using Horner's method
    BOOST_MATH_GPU_ENABLED blst_scalar poly_evaluate(polynomial& a, const blst_scalar& x)
    {
        blst_scalar result = a.back();
        for (size_t i = a.size() - 1; i-- > 0; )
        {
            blst_sk_mul_n_check(&result, &result, &x);
            blst_sk_add_n_check(&result, &result, &a[i]);
        }
        return result;
    }
};

using r1cs= vector<vector<unordered_map<size_t,blst_scalar>>>; // 0:A , 1:B, 2:C
using namespace Polynomial;
//singleton class constrain 
class Constrain {
private:
    Constrain() {}
    //delete copy constructor and assignment
    Constrain(const Constrain&)= delete ;
    Constrain& operator = (const Constrain&) = delete;
public:
    static size_t nConstraints, nVars,nPubInputs;
    static r1cs R1CS;
    static size_t f_x; //cyclotomic polynomial power of 2 close to nConstraints
    const static blst_scalar omega; //this is 2^20th root of unity in BLS prime field
public:
    static void setup(string);
    static void print_r1cs();
    static void vanishing_polynomial(){
        std::cout<<"x^"<<f_x<<" -1\n";
    }
};
size_t Constrain::nConstraints = 0; //row
size_t Constrain::nVars = 0; //column
size_t Constrain::nPubInputs=0;
r1cs Constrain::R1CS ={};
size_t::Constrain::f_x = 1;
const blst_scalar Constrain::omega = { // little ending
        0x4B, 0x8D, 0x89, 0x39,
        0x0E, 0x7E, 0xCE, 0xFE,
        0xD9, 0x09, 0x5E, 0x26,
        0x2D, 0xE0, 0x69, 0x2F,
        0x4A, 0xDE, 0x98, 0xCB,
        0x07, 0x6E, 0x7A, 0xA5,
        0x35, 0x70, 0x94, 0xCB,
        0x4B, 0xC5, 0xE1, 0x03
    }; 
//input path of r1cs json data 
void Constrain::setup(string path) {
    std::ifstream file(path);
    if(!file.is_open()) {
        std::cerr<<"failed to open the file";
        file.close();
        exit(0);
    }
    json data;
    file >> data;
    file.close();
    nConstraints= data["nConstraints"];
    nVars = data["nVars"];
    size_t nOutputs=data["nOutputs"];
    nPubInputs=data["nPubInputs"]; //public-input | remaining are all private-input
    nPubInputs+=nOutputs;
    auto helper= [](nlohmann::json_abi_v3_12_0::detail::iter_impl<nlohmann::json_abi_v3_12_0::json> begin,
        nlohmann::json_abi_v3_12_0::detail::iter_impl<nlohmann::json_abi_v3_12_0::json> end)
        ->unordered_map<size_t,blst_scalar>{ //helper lamda function to extract constrain from json
        unordered_map<size_t,blst_scalar>out;
        vector<byte> byte;
        blst_scalar temp;
        for(auto item= begin; item!=end ; ++item) {
            cpp_int value(item.value().get<std::string>());
            //extract byte and provide to blst.
            boost::multiprecision::export_bits(value,std::back_inserter(byte),8);
            blst_scalar_from_be_bytes(&temp,byte.data(),byte.size());
            out[std::stoull(item.key())] = temp;
            byte.clear();
        }
        return out;
    };
    R1CS.reserve(nConstraints);
    for(auto &x: data["constraints"]) {
        R1CS.push_back({
            helper(x[0].begin(),x[0].end()),// A
            helper(x[1].begin(),x[1].end()), // B
            helper(x[2].begin(),x[2].end()) // C
        });
    }
    data.clear();
    f_x = 1ll << (int)ceil(log2(nConstraints)); //log2 gives the power of 2 we require
    std::cout<<"Finished reading up the test.json\n";
}

void Constrain::print_r1cs() {
    for(auto &x:R1CS){
        std::cout<<"\n{\n  ";
        for(auto &y: x[0]) std::cout<<y.first<<": "<<y.second<<std::endl;
        std::cout<<"}\n{\n  ";
        for(auto &y: x[1]) std::cout<<y.first<<": "<<y.second<<std::endl;
        std::cout<<"}\n{\n  ";
        for(auto &y: x[2]) std::cout<<y.first<<": "<<y.second<<std::endl;
        std::cout<<"}\n";
    }
}

/*
It takes significant time since we are 3.nmlogm
Polynomial::polynomial Constrain::QAP_helper(size_t column,size_t con) { //con = A or B or C to work with , column is key
    blst_scalar zero;
    std::memset(zero.b,0,32);
    polynomial point_value(nConstraints, zero);
    //perform InvNTT: first capture the column's of matrix
    for(size_t i=0;i<nConstraints;i++) {
        if(R1CS[i][con].count(column)) point_value[i] = R1CS[i][con][column];
    }
    //we need to choose omega accordingly: provided only 2^20th root: we can repeateadly square it f_x = log2(nConstrain)
    blst_scalar om= modular_exp(omega,1 << (20- (int)log2(f_x)));// fx is the power of cyclotomic polynomial
    return invNTT(om,f_x,point_value);
    //note prover can do better and BLS have max subgroup of order 2^32.
}
//we will do it at once in a single loop in thread:
#include<thread>
void Constrain::QAP(vector<polynomial>&A,vector<polynomial>&B,vector<polynomial>&C) { 
    A.resize(nVars),B.resize(nVars),C.resize(nVars);
    auto computeA = [&]() {
        for(size_t i = 0; i < nVars; i++) {
            A[i] = QAP_helper(i, 0);
        }
    };
    auto computeB = [&]() {
        for(size_t i = 0; i < nVars; i++) {
            B[i] = QAP_helper(i, 1);
        }
    };
    auto computeC = [&]() {
        for(size_t i = 0; i < nVars; i++) {
            C[i] = QAP_helper(i, 2);
        }
    };
    std::thread t1(computeA);
    std::thread t2(computeB);
    std::thread t3(computeC);
    t1.join();
    t2.join();
    t3.join();
}
*/

