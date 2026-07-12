#include"lib/prover.hpp"
int main() {
    Constrain::setup("C:/programming/ZK-C/Pairing/lib/test.json");
    Prover prover = Prover("C:/programming/ZK-C/Pairing/lib/witness.json");
    Constrain::lagrange_basis();// we just need this only once
    prover.QAP();
    prover.write_proof();
    
    return 0;
}