#include<iostream>
#include<blst.h>
#include<nlohmann/json.hpp>
#include<fstream>
using json= nlohmann::json;
using std::string;
void print(byte* b,size_t size) {
    for(byte* x= b; x < b+size;x++) {
        std::cout<<std::hex<<std::setw(2)<<std::setfill('0')<<int(*x);
    }
    std::cout<<std::endl;
}
blst_p1_affine read_p1(string item) {
    byte out[96];
    string temp;
    temp.resize(2);
    size_t j=0;
    for(size_t i=0;i<item.length();i+=2) {
        temp[0]=item[i], temp[1]=item[i+1];
        out[j++] = std::stoi(temp,nullptr,16);
    }
    blst_p1_affine result;
    blst_p1_deserialize(&result,out);
    if(!blst_p1_affine_on_curve(&result)) {
        std::cerr<<"Point not in G1";
        exit(1);
    }
    print(out,96);
    return result;
}
blst_p2_affine read_p2(string item) {
    byte out[192];
    string temp;
    temp.resize(2);
    size_t j=0;
    for(size_t i=0;i<item.length();i+=2) {
        temp[0]=item[i], temp[1]=item[i+1];
        out[j++] = std::stoi(temp,nullptr,16);
    }
    blst_p2_affine result;
    blst_p2_deserialize(&result,out);
    if(!blst_p2_affine_on_curve(&result)){
        std::cerr<<"Point not in G2";
        exit(1);
    }
    print(out,192);
    return result;
}

    //pairing 0=[-A].[B] +[C].G2

bool Groth16(blst_p1_affine&A, blst_p2_affine&B, blst_p1_affine&C,
    blst_p1_affine& alpha, blst_p2_affine& beta){
    blst_fp12 result; // output of pairing
    blst_p2_affine generator = *blst_p2_affine_generator();
    blst_p1_affine* P[3]={
        &A,
        &alpha,
        &C
    };// three G1 points
    blst_p2_affine* Q[3]={
        &B,
        &beta,
        &generator
    }; // three G2 points including generator
    blst_miller_loop_n(&result,Q,P,3);
    blst_final_exp(&result,&result);
    byte out[576];
    blst_bendian_from_fp12(out,&result);
    print(out,576);
    return blst_fp12_is_one(&result);
}
int main() {
    json proof,setup;
    std::ifstream file("proof.json");
    if(!file.is_open()){
        std::cerr<<"failed to read proof.json!";
        file.close();
        exit(1);
    }
    file >> proof;
    file.close();
    file.open("setup.json");
    if(!file.is_open()){
        std::cerr<<"failed to read setup.json!";
        file.close();
        exit(1);
    }
    file >> setup;
    file.close();
    blst_p1_affine A = read_p1(proof["A"].get<string>());
    blst_p2_affine B= read_p2(proof["B"].get<string>());
    blst_p1_affine C= read_p1(proof["C"].get<string>());
    blst_p1_affine alpha= read_p1(setup["alpha"].get<string>());
    blst_p2_affine beta = read_p2(setup["beta"].get<string>());
    proof.clear();setup.clear();
    blst_fp_cneg(&A.y,&A.y,true); // -A
    std::cout<< Groth16(A,B,C,alpha,beta);
   return 0;
}