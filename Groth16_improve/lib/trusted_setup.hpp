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
    blst_scalar gamma, delta;// gamma for public-input and delta for private input
    json obj;
    blst_scalar f_x;//evaluate vanishing polynomial at r
public:
    Trusted_setup() {
        uint64_t random_block[4]={1,0,0,0};
        blst_scalar_from_uint64(&one,random_block); //1
        get_rand(this->r,random_block);
        get_rand(this->alpha,random_block);
        get_rand(this->beta,random_block);
        get_rand(this->gamma,random_block);
        get_rand(this->delta,random_block);
        blst_p1 p1;
        blst_p2 p2;
        blst_sk_to_pk_in_g1(&p1,&alpha);
        blst_sk_to_pk_in_g2(&p2,&beta);
        blst_p1_serialize(out_G1,&p1);
        blst_p2_serialize(out_G2,&p2);
        obj["alpha"]=points_string(out_G1,G1_SIZE);
        obj["beta"] = points_string(out_G2,G2_SIZE);

        blst_sk_to_pk_in_g2(&p2,&gamma);
        blst_p2_serialize(out_G2,&p2);
        obj["gamma"]=points_string(out_G2,G2_SIZE);
        blst_sk_to_pk_in_g2(&p2,&delta);
        blst_p2_serialize(out_G2,&p2);
        obj["delta"]=points_string(out_G2,G2_SIZE);
        //evaluation of vanishing polynomial always in the form of x^n-1
        f_x=modular_exp(this->r,Constrain::f_x);
        if(!blst_sk_sub_n_check(&f_x,&f_x,&one)){
            std::cerr<<"random value turns out to be one of root so rerun!";
            exit(1);
        }
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
    //we can get R1CS from constrain so we will direct evaluate on point-form
    blst_scalar barycentric(vector<blst_scalar>&,const blst_scalar&,const blst_scalar&,size_t);//return scalar after combining A,B,C

};

void Trusted_setup::init_A_B() {
    json arrayG1= json::array(); //G1 element
    json arrayG2=json::array(); //G2 element
    json arrayPG=json::array();
    blst_scalar dummy=one,p=f_x; //p ->f(r)rG1
    blst_p1 p1;
    blst_p2 p2;
    for(size_t i=0;i<Constrain::f_x;i++) { // usually we have degree nConstrain but we are using NTT so we will consider higer polynomial
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
    //this is used by prover which are all private so include it
    blst_sk_inverse(&delta,&delta),blst_sk_inverse(&gamma,&gamma); //as we will be dividing srs with these values
    blst_sk_mul_n_check(&p,&p,&delta);
    for(size_t i=0; i <Constrain::f_x - 1;i++){
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

//here is what we need barycentric evaluation technique.
void Trusted_setup::Tau() {
    const blst_scalar omega= modular_exp(Constrain::omega,1 << (20 - (int)log2(Constrain::f_x)));
    blst_scalar left;//left part of barycentric evaluation: r^n-1/n
    uint64_t block[4]={Constrain::f_x,0,0,0};
    blst_scalar_from_uint64(&left,block); blst_sk_inverse(&left,&left);
    blst_sk_mul_n_check(&left,&left,&f_x);
    //we can precompute the denominator section which is r-omega's
    blst_scalar temp=one;
    vector<blst_scalar>denominator(Constrain::nConstraints);
    for(size_t i=0;i<Constrain::nConstraints;i++){; //here we don't need to go upto f_x since higher evaluation is 0
        blst_sk_sub_n_check(&denominator[i],&r,&temp);
        blst_sk_inverse(&denominator[i],&denominator[i]);
        blst_sk_mul_n_check(&temp,&temp,&omega);
    } //now we need y_i*omega's
    blst_p1 p1;
    json array = json::array();
    for(size_t i=0;i<Constrain::nVars;i++) {
        blst_scalar eval=barycentric(denominator,left,omega,i);
        blst_sk_to_pk_in_g1(&p1,&eval);
        blst_p1_serialize(out_G1,&p1);
        array.push_back(points_string(out_G1,G1_SIZE));
    }
    obj["tau"] = array;
}
blst_scalar Trusted_setup::barycentric(vector<blst_scalar>&denominator,const blst_scalar& left,const blst_scalar& omega,size_t column) {
    blst_scalar A,B,C,temp=one,num1,num2,num3;
    std::memset(A.b,0,32),std::memset(B.b,0,32),std::memset(C.b,0,32);
    for(size_t i=0;i<Constrain::nConstraints;i++) {
        if(Constrain::R1CS[i][0].count(column)){ //A
            blst_sk_mul_n_check(&num1,&temp,&Constrain::R1CS[i][0][column]);
            blst_sk_mul_n_check(&num1,&num1,&denominator[i]);
            blst_sk_add_n_check(&A,&A,&num1);
        }
        if(Constrain::R1CS[i][1].count(column)){ //B
            blst_sk_mul_n_check(&num2,&temp,&Constrain::R1CS[i][1][column]);
            blst_sk_mul_n_check(&num2,&num2,&denominator[i]);
            blst_sk_add_n_check(&B,&B,&num2);
        }
        if(Constrain::R1CS[i][2].count(column)){ //C
            blst_sk_mul_n_check(&num3,&temp,&Constrain::R1CS[i][2][column]);
            blst_sk_mul_n_check(&num3,&num3,&denominator[i]);
            blst_sk_add_n_check(&C,&C,&num3);
        }
        blst_sk_mul_n_check(&temp,&temp,&omega);
    }// final step include alpha beta and add
    blst_sk_mul_n_check(&A,&A,&left);
    blst_sk_mul_n_check(&B,&B,&left);
    blst_sk_mul_n_check(&C,&C,&left);
    blst_scalar result;
    blst_sk_mul_n_check(&A,&A,&beta),blst_sk_mul_n_check(&B,&B,&alpha);
    blst_sk_add_n_check(&temp,&A,&B);
    blst_sk_add_n_check(&result,&temp,&C);
    //we have to careful which to use gamma or delta which is given by PubInputs
    //simply we can check if column >= pubInputs then they are all private inputs
    blst_sk_mul_n_check(&result,&result,(column <=Constrain::nPubInputs)?&gamma:&delta);
    //we get alpha.B(r)+beta.A(r)+C(r)
    return result;
}