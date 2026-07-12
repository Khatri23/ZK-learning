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
using r1cs= vector<vector<unordered_map<size_t,blst_scalar>>>; // 0:A , 1:B, 2:C

std::ostream&  operator <<(std::ostream& Cout,blst_scalar& s) { //print blst_scalar in hex
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
    BOOST_MATH_GPU_ENABLED polynomial ply_multiply(polynomial& a, polynomial& b) {
        blst_scalar zero;
        std::memset(zero.b,0,32);
        const size_t n= a.size()-1, m= b.size()-1;
        polynomial result(n+m+1,zero);
        blst_scalar temp;
        for(size_t i=0;i<=n;i++) {
            for(size_t j=0;j<=m;j++) {
                blst_sk_mul_n_check(&temp,&a[i],&b[j]);
                blst_sk_add_n_check(&result[i+j],&result[i+j],&temp);
            }
        }
        return result;  
    }
    BOOST_MATH_GPU_ENABLED polynomial operator *(polynomial&a ,polynomial& b)
    {
        return ply_multiply(a,b);
    }

    BOOST_MATH_GPU_ENABLED void impl_div(polynomial& q, polynomial& r,polynomial& divisor ,long long &k, size_t & n,blst_scalar& inv) {
        blst_sk_mul_n_check(&q[k],&inv,&r[n+k]);
        blst_scalar temp;
        for(long long int i=n;i>=0;i--) {
            blst_sk_mul_n_check(&temp,&q[k],&divisor[i]);
            blst_sk_sub_n_check(&r[i+k],&r[i+k],&temp);
        }
    }

    BOOST_MATH_GPU_ENABLED polynomial poly_divide(polynomial& dividend, polynomial& divisor) { //no remainder
        //divisor element must not zero in first place 
        size_t n=divisor.size()-1;
        size_t m=dividend.size()-1;
        if(n > m){
            std::cerr<<"Divisor is greater than dividend";
            exit(1);
        }
        blst_scalar inv;
        blst_sk_inverse(&inv,&divisor[n]);
        long long k = m-n; 
        polynomial quotent(k+1);
        polynomial remainder(dividend.begin(),dividend.end());
        do{
            impl_div(quotent,remainder,divisor,k,n,inv);
        }while(k-- != 0);
        // for(auto &x:remainder) std::cout<<x<<std::endl; //remainder
        return quotent;
    }
    BOOST_MATH_GPU_ENABLED polynomial poly_add(polynomial & a, polynomial &b) { 
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
    BOOST_MATH_GPU_ENABLED polynomial operator +(polynomial&a,polynomial& b) {
        return poly_add(a,b);
    }
    BOOST_MATH_GPU_ENABLED polynomial poly_subtract(polynomial& a, polynomial& b) {
        polynomial result(a.begin(),a.end());
        for(size_t i=0;i<b.size();i++) blst_sk_sub_n_check(&result[i],&result[i],&b[i]);
        return result;
    }
    BOOST_MATH_GPU_ENABLED void poly_scalar_mul(polynomial& a, blst_scalar& b){
        for(auto &x:a) blst_sk_mul_n_check(&x,&x,&b);
    }
     //evaluate the polynomial at a given value
    BOOST_MATH_GPU_ENABLED blst_scalar poly_evaluate(polynomial& a,blst_scalar& x) {
        blst_scalar result=a[0],temp;
        blst_scalar t=x;
        for(size_t i=1;i<a.size();i++) {
            blst_sk_mul_n_check(&temp,&a[i],&t);
            blst_sk_add_n_check(&result,&result,&temp);
            blst_sk_mul_n_check(&t,&x,&t);
        }
        return result;
    }

    std::ostream& operator <<(std::ostream& COUT,polynomial& a) {
        COUT<<"{ ";
        for(auto &x:a) COUT<<x<<" ,";
        COUT<<"}";
        return COUT;
    }
};


//singleton class constrain 
class Constrain {
private:
    Constrain() {}
    //delete copy constructor and assignment
    Constrain(const Constrain&)= delete ;
    Constrain& operator = (const Constrain&) = delete;
    static void vanishing_polynomial();
    static Polynomial::polynomial QAP_helper(size_t,size_t);
public:
    static size_t nConstraints, nVars,nPubInputs,nOutputs;
    static r1cs R1CS;
    static vector<Polynomial::polynomial> l_basis; //lagrange basis polynomial
    static Polynomial::polynomial f_x ; //vanishing polynomial
public:
    static void setup(string);
    static void print_r1cs();
    static void lagrange_basis();
    static vector<Polynomial::polynomial> QAP(char ); // Quadratic Arithmetic Program
};
size_t Constrain::nConstraints = 0; //row
size_t Constrain::nVars = 0; //column
size_t Constrain::nOutputs=0;
size_t Constrain::nPubInputs=0;
r1cs Constrain::R1CS ={};
vector<Polynomial::polynomial> Constrain::l_basis = {};
Polynomial::polynomial Constrain::f_x = {};
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
    nOutputs=data["nOutputs"];
    nPubInputs=data["nPubInputs"];
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
    vanishing_polynomial();
    data.clear();
}
// complete the construction of polynomial from lagrange interpolation!
Polynomial::polynomial Constrain::QAP_helper(size_t column,size_t con) { //con = A or B or C to work with , column is key
    using namespace Polynomial;
    blst_scalar zero;
    std::memset(zero.b,0,32);
    polynomial result(nConstraints, zero); //lagrange basis size is equal to row since it will have degree= row -1 
    for(size_t i=0;i<nConstraints;i++) {//rows
        if(R1CS[i][con].count(column)) { // if key exist in map
            polynomial temp= l_basis[i] ; // extract the lagrange basis of corresponding index
            poly_scalar_mul(temp,R1CS[i][con][column]);
            result = result + temp;
        }
    }
    return result;
}
vector<Polynomial::polynomial>Constrain::QAP(char choice) { //because of homomorphism between polynomial & vector this is optional for prover
    vector<Polynomial::polynomial>output(nVars);
    //apply lagrange interpolation to columns to transform into polynomial as a result we will get 
    //polynomials equal to size of witness!
    switch(choice){
        case 'A':
            for(size_t i=0;i<nVars;i++) { //column is equal to the size of the witness!
                output[i]=QAP_helper(i,0);
            }
            break;
        case 'B':
            for(size_t i=0;i<nVars;i++) { //column is equal to the size of the witness!
                output[i]=QAP_helper(i,1);
            }
            break;
        case 'C':
            for(size_t i=0;i<nVars;i++) { //column is equal to the size of the witness!
                output[i]=QAP_helper(i,2);
            }
            break;
        default :
            std::runtime_error("Constrain choice is invalid");
    };
    return output;
}

void Constrain::vanishing_polynomial() {
    using namespace Polynomial;
    blst_scalar zero,one;
    std::memset(zero.b,0,32);
    uint64_t value[4]={1,0,0,0};
    blst_scalar_from_uint64(&one,value);
    blst_scalar data;
    polynomial res={one};
    for(size_t i=0;i<nConstraints;i++) {
        value[0]=i;
        blst_scalar_from_uint64(&data,value);
        blst_sk_sub_n_check(&data,&zero,&data); // -i
        polynomial temp={data,one}; // x-i
        res = res * temp; 
    }
    f_x=res;
}

void Constrain::lagrange_basis() { // 0...nConstraints
    using namespace Polynomial;
    uint64_t value[4]={1,0,0,0,};
    blst_scalar one,zero;
    std::memset(zero.b,0,32);
    blst_scalar_from_uint64(&one,value);
    blst_scalar denominator,d,coeff;
    l_basis.resize(nConstraints);
    for(size_t i=0;i<nConstraints;i++) {
        denominator = one;
        value[0]=i;
        blst_scalar_from_uint64(&coeff,value);
        polynomial numerator={one}; //the same 1 value is copied
        for(size_t j=0;j<nConstraints;j++) {
            if(i==j) continue;
            value[0]=j;
            blst_scalar_from_uint64(&d,value);
            blst_sk_sub_n_check(&d, &zero, &d); // -j
            polynomial n={d,one}; //(x-j)
            numerator = numerator * n;
            blst_sk_add_n_check(&d,&coeff,&d); // i-j
            blst_sk_mul_n_check(&denominator,&denominator,&d);
        }
        blst_sk_inverse(&denominator,&denominator);
        poly_scalar_mul(numerator,denominator); // result in numerator!
        l_basis[i]=numerator;
    }
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



