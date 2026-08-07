#pragma once
#include"constrain.hpp"

using namespace Polynomial;
//prover that is responsible for providing valid witness that satisfy the constrain!
class Prover {
private:
    vector<blst_scalar> witness;
    blst_scalar impl_test1(unordered_map<size_t,blst_scalar>&);
    blst_p1 inner_product(polynomial& a, auto&,bool) ; //inner product which performs scalar multiplication and point addition
    blst_p2 inner_product(polynomial& b, auto&);
    std::string points_string(byte* out, size_t size) {
        std::stringstream ss;
        for(byte* x= out; x < out+size;x++) {
            ss << std::hex<<std::setw(2) <<std::setfill('0')<< int(*x);
        }
        return ss.str();
    }
    void setup_A_B_H(blst_p1&, blst_p2&, blst_p1&,json&);
public:
    Prover(string path);
    void show_witness() {
        std::cout<<"[\n";
        for(auto &x:witness){
            std::cout<<"  "<<x<<std::endl;
        }
        std::cout<<"]\n";
    }
    // check A.w o B.w == C.w perform matrix vector multiplication
    bool test1();
    //QAP and witness usage
    void QAP(); //initialize A(x),B(x),C(x) -> one time call 
    void write_proof();
public:
    polynomial A_x,B_x,C_x,H_x;
};

Prover::Prover(string path) {
    json data;
    std::ifstream file(path);
    if(!file.is_open()) {
        std::cerr<<"Failed to open witness";
        exit(1);
    }
    file >> data;
    file.close();
    if(data.size() != Constrain::nVars){
        std::cerr<<"Witness size does't match the column!";
        exit(1);
    }
    vector<byte>byte;
    blst_scalar sc;
    witness.reserve(data.size());
    for(auto item = data.begin();item!=data.end();++item) {
        cpp_int value(item.value().get<string>());
        boost::multiprecision::export_bits(value,std::back_inserter(byte),8);
        blst_scalar_from_be_bytes(&sc,byte.data(),byte.size());
        byte.clear();
        witness.push_back(sc);
    }
    data.clear();
    std::cout<<"finished reading up witness json!\n";
}

blst_scalar Prover::impl_test1(unordered_map<size_t,blst_scalar>&c) { //row-column multiplication 
    blst_scalar sum ;
    std::memset(sum.b,0,32);
    for(auto &x: c) {
        blst_scalar temp;
        //dense matrix is avoided since there will be bunch of 0 we only concern for the column which have value
        blst_sk_mul_n_check(&temp,&witness[x.first],&x.second) ; //boolean type return false if 0
        blst_sk_add_n_check(&sum,&sum,&temp);
    }
    return sum;
}
bool Prover::test1() {
    bool output= true;
    size_t n = Constrain::R1CS.size();
    vector<blst_scalar>A(n),B(n),C(n); // result vector size equal to the constrain
    for(size_t i=0;i<n;i++) {
        A[i]=impl_test1(Constrain::R1CS[i][0]);
        B[i]=impl_test1(Constrain::R1CS[i][1]);
        C[i]=impl_test1(Constrain::R1CS[i][2]);
    }
    for(auto &x: A) std::cout<<x <<std::endl;
    std::cout<<std::endl;
    for(auto &x:B) std::cout<<x<<std::endl;
    std::cout<<std::endl;
    for(auto &x:C) std::cout<<x<<std::endl;
    //element wise multiplication result in A as well as subtraction where result in C should be 0
    std::cout<<"\nA.w o B.w \t\t\t\t\t\t\t\t\t\t\t\t C\n";
    for(size_t i=0;i<n;i++) {
        blst_sk_mul_n_check(&A[i],&A[i],&B[i]) ;
        std::cout<<A[i]<<"\t"<<C[i]<<std::endl;
        output =output && !blst_sk_sub_n_check(&C[i],&A[i],&C[i]); //true if 0 
    }
    return output;
}
// it also calcualte balancing polynomial!
void Prover::QAP() {
    //perform matrix vector multiplication first
    vector<blst_scalar> A(Constrain::nConstraints),B(Constrain::nConstraints),C(Constrain::nConstraints);
    for(size_t i=0;i<Constrain::nConstraints;i++) {
        A[i]=impl_test1(Constrain::R1CS[i][0]);
        B[i]=impl_test1(Constrain::R1CS[i][1]);
        C[i]=impl_test1(Constrain::R1CS[i][2]);
    } // interpolate
    blst_scalar omega= modular_exp(Constrain::omega,1 << (20 - (int)log2(Constrain::f_x)));
    this->A_x=invNTT(omega,Constrain::f_x,A);
    this->B_x=invNTT(omega,Constrain::f_x,B);
    this->C_x=invNTT(omega,Constrain::f_x,C);
    //we need to choose the omega since we will move to f_x+fx domain for multiplication since we require 2f_x points
    omega= modular_exp(Constrain::omega,1 << (19 - (int)log2(Constrain::f_x)));
    auto AB_x = poly_multiply(omega,Constrain::f_x*2,A_x,B_x);
    AB_x = poly_subtract(AB_x, this->C_x);
    this->H_x = poly_divide(AB_x, Constrain::f_x);
}

//if wtf is true we are using tau which we should only interating from private input which is starting from nPubInput
blst_p1 Prover::inner_product(polynomial& a, auto& srs,bool wtf){
    if(srs.size() != a.size()) std::runtime_error("SRS mismatch!");
    byte out[G1_SIZE];
    std::string temp;
    temp.resize(2);
    blst_p1 result,o,points; //points: store scalar multiplication , o: deserialized value of point 
    for(size_t i=(wtf)?Constrain::nPubInputs+1:0; i< srs.size();i++) {
        std::string item= srs[i];
        size_t j=0;
        for(size_t i=0;i<item.length();i+=2) { // read the SRS string in bytes
            temp[0]=item[i], temp[1]=item[i+1];
            out[j] = std::stoi(temp,nullptr,16);
            j++;
        }
        blst_p1_affine affine1;
        blst_p1_deserialize(&affine1,out);
        if(!blst_p1_affine_on_curve(&affine1)){
            std::cerr<<"Not an elliptic curve point G1";
            exit(1);
        }
        blst_p1_from_affine(&o,&affine1);//convert to homogeneous coordinate!
        blst_p1_mult(&points,&o,a[i].b,256);
        if(i==0 || ((i==Constrain::nPubInputs+1) & wtf)) result = points;
        else blst_p1_add(&result,&result,&points);
    }
    return result;
}
blst_p2 Prover::inner_product(polynomial& a, auto& srs) {
    if(srs.size() != a.size()) std::runtime_error("SRS mismatch!");
    byte out[G2_SIZE];
    std::string temp;
    temp.resize(2);
    blst_p2 result,o,points; //points: store scalar multiplication , o: deserialized value of point 
    size_t i=0;//index for polynomial aka vector<blst_scalar>
    for(std::string item: srs) {
        size_t j=0;
        for(size_t i=0;i<item.length();i+=2) {
            temp[0]=item[i], temp[1]=item[i+1];
            out[j++] = std::stoi(temp,nullptr,16);
        }
        blst_p2_affine affine2;
        blst_p2_deserialize(&affine2,out);
        if(!blst_p2_affine_on_curve(&affine2)){
            std::cerr<<"Not an elliptic curve point G1";
            exit(1);
        }
        blst_p2_from_affine(&o,&affine2);
        blst_p2_mult(&points,&o,a[i].b,256);
        if(i==0) result = points;
        else blst_p2_add(&result,&result,&points);
        i++;
    }
    return result;
}

void Prover::write_proof() {
    json obj;
    std::ifstream file("setup.json");
    if(!file.is_open()){
        std::cerr<<"Error";
        file.close();
    }
    file >> obj;
    file.close();
    blst_p1 A, H;
    blst_p2 B;
    setup_A_B_H(A,B,H,obj);
    blst_p1 C= inner_product(witness,obj["tau"],true); // it is the inner product with the witness
    blst_p1_add(&C,&C,&H); //point addition with H
    obj.clear();
    //write to json
    byte sk[32];
    json array=json::array();
    for(size_t i=0;i<=Constrain::nPubInputs;i++) { //1 is also included 
        blst_bendian_from_scalar(sk,&witness[i]);
        array.push_back(points_string(sk,32));
    }
    obj["PublicInput"]=array;

    byte out_G1[G1_SIZE],out_G2[G2_SIZE];
    blst_p1_serialize(out_G1,&A);
    obj["A"]=points_string(out_G1,G1_SIZE);
    blst_p2_serialize(out_G2,&B);
    obj["B"]=points_string(out_G2,G2_SIZE);
    blst_p1_serialize(out_G1,&C);
    obj["C"] =points_string(out_G1,G1_SIZE);
    std::ofstream out("proof.json");
    out << obj.dump(4);
    out.close();
    obj.clear();
    std::cout<<"Proof written to proof.json!";
}

void Prover::setup_A_B_H(blst_p1& A, blst_p2& B, blst_p1& H,json& obj) {
    byte out_G1[G1_SIZE] , out_G2[G2_SIZE];
    A= inner_product(A_x,obj["srsG1"],false);
    B= inner_product(B_x,obj["srsG2"]);
    H= inner_product(H_x,obj["srsPOLY"],false);
    string alpha= obj["alpha"].get<string>(),beta=obj["beta"].get<string>(),temp;
    temp.resize(2);
    size_t j=0;
    for(size_t i=0;i<alpha.length();i+=2){
        temp[0]=alpha[i],temp[1]=alpha[i+1];
        out_G1[j++] = std::stoi(temp,nullptr,16);
    }
    j=0;
    blst_p1_affine affineP1;
    blst_p2_affine affineP2;
    blst_p1_deserialize(&affineP1,out_G1); //alpha
    if(!blst_p1_affine_on_curve(&affineP1)){
        std::cerr<<"alpha not in G1";
        exit(2);
    }
    for(size_t i=0;i<beta.length();i+=2){
        temp[0]=beta[i],temp[1]=beta[i+1];
        out_G2[j++]=std::stoi(temp,nullptr,16);
    }
    blst_p2_deserialize(&affineP2,out_G2);
    if(!blst_p2_affine_on_curve(&affineP2)){
        std::cerr<<"beta not in G2";
        exit(2);
    } 
    //perform point addition
    blst_p1_add_affine(&A,&A,&affineP1);
    blst_p2_add_affine(&B,&B,&affineP2);
}