#include "lib/trusted_setup.hpp"
#include<chrono>
using namespace Polynomial;

int main() {
    auto start = std::chrono::steady_clock::now();
    Constrain::setup("D:/Groth-16/lib/test.json");
    Trusted_setup obj;
    obj.publish();
    auto end = std::chrono::steady_clock::now();
    double ms = std::chrono::duration<double, std::milli>(end - start).count();
    std::cout << "Trusted Setup: " << ms << " ms\n";
    return 0;
}