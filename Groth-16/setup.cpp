#include "lib/trusted_setup.hpp"

int main() {
    Constrain::setup("C:/programming/ZK-C/Pairing/lib/test.json");
    Constrain::lagrange_basis();
    Trusted_setup obj;
    obj.publish();    
    return 0;
}