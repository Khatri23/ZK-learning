#include"lib/prover.hpp"
#include<chrono>
int main() {
    auto start = std::chrono::steady_clock::now();
    Constrain::setup("D:/Groth-16/lib/test.json");
    Prover prover = Prover("D:/Groth-16/lib/witness.json");
    prover.QAP();
    prover.write_proof();
    auto end = std::chrono::steady_clock::now();
    double ms = std::chrono::duration<double, std::milli>(end - start).count();
    std::cout << "\nProver: " << ms << " ms\n";
    
    uint64_t var[4]={334,323,122,2956};
    blst_scalar r,one;
    blst_scalar_from_uint64(&r,var);
    var[0]=1,var[1]=var[2]=var[3]=0;
    blst_scalar_from_uint64(&one,var);
    blst_scalar A,B,C,H;
    A=poly_evaluate(prover.A_x,r), B=poly_evaluate(prover.B_x,r), C=poly_evaluate(prover.C_x,r), H=poly_evaluate(prover.H_x,r);
    blst_sk_mul_n_check(&A,&A,&B);
    r=modular_exp(r,Constrain::f_x); blst_sk_sub_n_check(&r,&r,&one);
    blst_sk_mul_n_check(&H,&H,&r);
    blst_sk_add_n_check(&C,&C,&H);
    std::cout<<A<<std::endl;
    std::cout<<C<<std::endl;
    return 0;
}
