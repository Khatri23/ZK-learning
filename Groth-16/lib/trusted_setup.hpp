#pragma once
#include "constrain.hpp"
#include<random>
#include<sstream>
/*
    srsA {r^nG1, r^n-1G1...rG1,G1}
    srsB{r^nG2, r^n-1G2...rG2,G2}
    srsC= srsA since we just need srs for G1 and G2 and the Groth 16 is [A] . [B] = [C] . G2
    srsPOLY={r^nf(r)G1, r^n-1f(r)G1,...,rf(r)G1,f(r)G1} since h(x)f(x) is balancing polynomial and f(x) is vanishing
    that is easily known so first we evaluate the f(x) in r and the srs facilate multiplication on each coefficient of h(x) with f(x)
    along with evaluation with r this is same thing as giving r instead we are evaluating on the encryption value of r
    so the prover doesn't know what that r is(solving discrete log).
    we have to generate to accomodate the complete degree of polynomial.
    Prover performs the inner product with as <coefficient> <srs>
*/
std::string points_string(byte* out, size_t size) {
    std::stringstream ss;
    for(byte* x= out; x < out+size;x++) {
         ss << std::hex<<std::setw(2) <<std::setfill('0')<< int(*x);
    }
    return ss.str();
}
class Trusted_setup{
private:
    byte out_G1[G1_SIZE], out_G2[G2_SIZE]; //decerilize the point to bytes
    blst_scalar one;
    blst_scalar r,alpha,beta; //random value alpha,beta is used to force the prover to act honestly
    json obj;
    blst_scalar f_x;//evaluate vanishing polynomial at r
public:
    Trusted_setup() {
        uint64_t random_block[4]={1,0,0,0};
        blst_scalar_from_uint64(&one,random_block); //1
        get_rand(this->r,random_block);
        get_rand(this->alpha,random_block);
        get_rand(this->beta,random_block);
        blst_p1 p1;
        blst_p2 p2;
        blst_sk_to_pk_in_g1(&p1,&alpha);
        blst_sk_to_pk_in_g2(&p2,&beta);
        blst_p1_serialize(out_G1,&p1);
        blst_p2_serialize(out_G2,&p2);
        obj["alpha"]=points_string(out_G1,G1_SIZE);
        obj["beta"] = points_string(out_G2,G2_SIZE);
        f_x=Polynomial::poly_evaluate(Constrain::f_x,r);
        init_A_B();
        Tau();
    }
    void publish() {
        std::ofstream file("setup.json");
        file << obj.dump(4);
        file.close();
        obj.clear();
        std::cout<<"written in setup.json!\n";
    }
private:
    void init_A_B(); //srs for G1,G2 which is used by A,B
    void get_rand(blst_scalar& r,uint64_t* random_block) {
        //using a simple random 64 bit value not recommended for experimenting!
        std::random_device rd;
        std::mt19937_64 gen(rd());
        std::uniform_int_distribution<uint64_t>dis(0,std::numeric_limits<uint64_t>::max());
        do{
            random_block[0]=dis(gen), random_block[1]=dis(gen), random_block[2]=dis(gen), random_block[3]=dis(gen);
            blst_scalar_from_uint64(&r,random_block);
        }while(!blst_sk_check(&r)); //if 0 repeat!
        random_block[1]=random_block[2]=random_block[3]=0;
        random_block[0]=1;
    }
    void Tau();// alpha , beta is included in QAP so prover cannot evaluate alpha*B(x)+beta*A(x)
};

void Trusted_setup::init_A_B() {
    json arrayG1= json::array(); //G1 element
    json arrayG2=json::array(); //G2 element
    json arrayPG=json::array();
    blst_scalar dummy=one,p=f_x; //p ->f(r)rG1
    blst_p1 p1;
    blst_p2 p2;
    for(size_t i=0;i<Constrain::nConstraints;i++) { // polynomial degree= row size-1
        //compute the publickey on both G1 and G2
        blst_sk_to_pk_in_g1(&p1,&dummy);
        blst_sk_to_pk_in_g2(&p2,&dummy);
        blst_p1_serialize(out_G1,&p1);
        blst_p2_serialize(out_G2,&p2);
        arrayG1.push_back(points_string(out_G1,G1_SIZE)); //write to the json array!
        arrayG2.push_back(points_string(out_G2,G2_SIZE));
        if(!blst_sk_mul_n_check(&dummy,&dummy,&r)){
            std::cerr<<"zero value encounter re-run the process!";
            exit(1); // don't expect 0
        }
    }
    for(size_t i=0; i <Constrain::nConstraints - 1;i++){
        blst_sk_to_pk_in_g1(&p1,&p);
        blst_p1_serialize(out_G1,&p1);
        arrayPG.push_back(points_string(out_G1,G1_SIZE));
        if(!blst_sk_mul_n_check(&p,&r,&p)){
            std::cerr<<"zero value encounter re-run the process!";
            exit(1);
        }
     } //h(x) is quotent polynomial so it have degree 2*m -f_x.degree(m+1)
    obj["srsG1"] = arrayG1;
    obj["srsG2"] = arrayG2;
    obj["srsPOLY"] = arrayPG;
}

void Trusted_setup::Tau() {
    using namespace Polynomial;
    vector<polynomial> A= Constrain::QAP('A'), B=Constrain::QAP('B'), C=Constrain::QAP('C');
    //evaluate each of the polynomialson r include alpha and beta and convert to G1 points
    blst_p1 p1;
    blst_scalar a,b,c,res;
    json array = json::array();
    for(size_t i=0;i<Constrain::nVars;i++) {
        a=poly_evaluate(A[i],r);
        b=poly_evaluate(B[i],r);
        c=poly_evaluate(C[i],r);
        blst_sk_mul_n_check(&a,&a,&beta);
        blst_sk_mul_n_check(&b,&b,&alpha);
        blst_sk_add_n_check(&res,&a,&b);
        blst_sk_add_n_check(&res,&res,&c); //convert res to G1 points
        blst_sk_to_pk_in_g1(&p1,&res);
        blst_p1_serialize(out_G1,&p1);
        array.push_back(points_string(out_G1,G1_SIZE));
    }
    obj["tau"] = array;
}