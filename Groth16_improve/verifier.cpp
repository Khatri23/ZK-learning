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
    std::cout<<std::endl<<std::endl;
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
    print(out,96);
    if(!blst_p1_affine_on_curve(&result)) {
        std::cerr<<"Point not in G1";
        exit(1);
    }
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
    print(out,192);
    if(!blst_p2_affine_on_curve(&result)){
        std::cerr<<"Point not in G2";
        exit(1);
    }
    return result;
}

    //pairing 1=e([-A],[B])e([alpha],[beta])e([X],[gamma])e([C],[delta])

bool Groth16(blst_p1_affine&A, blst_p2_affine&B, blst_p1_affine&C,blst_p1_affine& alpha,
    blst_p2_affine& beta,blst_p2_affine&gamma, blst_p2_affine& delta, blst_p1_affine&x){
    //gamma for public-input used by x delta for private input used by C
    blst_fp12 result; // output of pairing
    blst_p1_affine* P[4]={
        &A, 
        &alpha,
        &x,
        &C
    };// three G1 points
    blst_p2_affine* Q[4]={
        &B,
        &beta,
        &gamma,
        &delta
    }; // three G2 points including generator
    blst_miller_loop_n(&result,Q,P,4);
    blst_final_exp(&result,&result);
    byte out[576];
    blst_bendian_from_fp12(out,&result);
    print(out,576);
    return blst_fp12_is_one(&result);
}
blst_p1_affine read_public_input(auto&PublicInput,auto&srs) {
    blst_p1_affine x;
    byte out[96],scalar[32];
    std::string temp;
    temp.resize(2);
    blst_p1 result,o,points; //points: store scalar multiplication , o: deserialized value of point 
    
    for(size_t i=0; i< PublicInput.size();i++) {
        std::string item= srs[i];
        size_t j=0;
        for(size_t i=0;i<item.length();i+=2) {
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
        //we need to convert the string of PublicInput to little-endian
        j=0;
        item=PublicInput[i];
        for(int k=item.length()-2; k>=0;k-=2){
            temp[0]=item[k],temp[1]=item[k+1];
            scalar[j++]=std::stoi(temp,nullptr,16);
        }
        blst_p1_mult(&points,&o,scalar,256);
        if(i==0) result = points;
        else blst_p1_add(&result,&result,&points);
    }
    blst_p1_to_affine(&x,&result);
    return x;
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
    std::cout<<"A: ";
    blst_p1_affine A = read_p1(proof["A"].get<string>());
    std::cout<<"B: ";
    blst_p2_affine B= read_p2(proof["B"].get<string>());
    std::cout<<"C: ";
    blst_p1_affine C= read_p1(proof["C"].get<string>());
    std::cout<<"alpha: ";
    blst_p1_affine alpha= read_p1(setup["alpha"].get<string>());
    std::cout<<"beta: ";
    blst_p2_affine beta = read_p2(setup["beta"].get<string>()); std::cout<<"gamma: ";
    blst_p2_affine gamma = read_p2(setup["gamma"].get<string>()); std::cout<<"delta: ";
    blst_p2_affine delta = read_p2(setup["delta"].get<string>());
    //we need to include srs to the public_input
    blst_p1_affine x = read_public_input(proof["PublicInput"],setup["tau"]);
    proof.clear();setup.clear();
    blst_fp_cneg(&A.y,&A.y,true); // -A
    std::cout<< Groth16(A,B,C,alpha,beta,gamma,delta,x);
   return 0;
}