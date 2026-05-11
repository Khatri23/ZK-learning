#pragma once
#include<iostream>
#include<vector>
#include<memory>
#include<boost/multiprecision/cpp_int.hpp>
#include<fstream>
#include<queue>
using boost::multiprecision::cpp_int;
using std::string,std::vector,std::shared_ptr;
enum OPERATOR{ADD,MUL,NONE};
#define Prime 4294967279
//Information of a node in tree of fan-in 2
class Node{
public:
    int value;
    string label;
    shared_ptr<Node>left;
    shared_ptr<Node>right;
    OPERATOR op;
    bool witness,helper;
    Node(){}
    Node(int value):op(NONE),witness(false),helper(false){
        this->value=value;
        left=NULL;
        right=NULL;
    }
    Node(OPERATOR op,shared_ptr<Node>left,shared_ptr<Node>right):witness(false),helper(false){
        this->op=op;
        switch (op)
        {
            case MUL:
                value=(left->value* right->value)%Prime;
                break;
            case ADD:
                value=(left->value + right->value) % Prime;
                break;
            case NONE: break;
        }
        this->left=left;
        this->right=right;
    }
    
};

cpp_int multiplicative_inverse(const cpp_int& a) {
    cpp_int u=a,v= Prime;
    cpp_int x1=1,x2=0;
    while(u != 1 && v != 1){
        while(!(u & 1)){
            u= u >> 1;
            if(!(x1 & 1)) x1=x1 >> 1;
            else x1=(x1+Prime) >> 1;
        }
        while(!(v & 1)) {
            v= v >> 1;
            if(!(x2 & 1)) x2=x2 >> 1;
            else x2=(x2+Prime) >> 1;
        }
        if(u >= v){
            u=u-v;
            x1-=x2;
        } else {
            v-=u;
            x2-=x1;
        }
    }
    cpp_int result;
    if (u == 1) result= x1 % Prime;
    else result= x2 % Prime;
    if(result < 0) result+=Prime;
    return result;
}
struct Little_Gate{
    vector<vector<cpp_int>>encode; //encodes parent, child
    OPERATOR op;
};

#include<cmath>
//we iterate label by label so we need to care about the gate value ADD, MULT -> its wiring predicate
// we also need to define the multilinear extension for gate value
//backend of <GKR>
class LabelInformation{
public:
    OPERATOR op;
    //[]->label [][][] encode the label of operator
    vector<Little_Gate>gate;//this will encode the current gate label & its neighbours
    //this will encode the current gate label & its neighbours
    vector<cpp_int>W;//function mapping {0,1}^k -> F where k is power of 2 since the total gate in each layer is 2^k
    
    //binds the L(r) to current gate label 
    void init(const vector<cpp_int>& parent, string& left,string& right,string & current,OPERATOR op){
        Look_operator(gate,parent,left,right,current,op);
    }
    
    //return's W(points)
    static cpp_int evaluateW(const vector<cpp_int>& W, const vector<cpp_int>&points) {
        //W is array of gate value at layer i.
        vector<cpp_int>intermedies;
        intermedies.reserve(W.size()); //points size is equal to the label which is no. of variables
        evaluateW(points,0,points.size(),1,intermedies);
        cpp_int result=0;
        for(size_t i=0;i<W.size();i++){
            result=(result + W[i]*intermedies[i])% Prime;
        }
        return result;
    }
    //defines the l(x) from random values again this returns the evaluation at p-1,p-2,... which is plug cpp_into W to send to verifier 
    static vector<cpp_int>Line(const vector<cpp_int>& l0,const vector<cpp_int>& l1,cpp_int x) {
        vector<cpp_int>points;
        points.reserve(l1.size());
        for(size_t i=0;i<l0.size();i++){
            cpp_int y= ((1-x)*l0[i] + x*l1[i])%Prime;
            if(y < 0) y+=Prime;
            points.push_back(y);
        }
        return points;
    }
    //lagrange interpolation for the line which evaluate directly constructing the polynomial at val
    static cpp_int Reconstruct_line(const vector<cpp_int>&basis, cpp_int val) {
        vector<cpp_int>x;
        x.reserve(basis.size());
        for(size_t i=0;i < basis.size();i++) {
            x.push_back(Prime-1-i); // 18,17... size varies based on layer
        }
        cpp_int sum=0;
        for(size_t i=0;i<x.size();i++){
            cpp_int numerator=basis[i],denominator=1;
            for(size_t j=0;j<x.size();j++) {
                if(i==j) continue;
                numerator=(numerator*(val-x[j])) % Prime;
                denominator=(denominator*(x[i]-x[j]))% Prime;
            }
            if(numerator < 0) numerator+=Prime;
            if(denominator < 0) denominator+=Prime;
            sum=(sum + numerator * multiplicative_inverse(denominator)) % Prime ;
        }
        return sum;
    }
private:
    void Look_operator(vector<Little_Gate>&value,const vector<cpp_int> parent, string& left,
        string& right,string& current,OPERATOR op){
        vector<vector<cpp_int>>array(3);//label of current and its child
        //information 
        array[0]=parent;
        for(size_t i=0;i<current.length();i++){
            if(current[i]=='0'){
                array[0][i]=1-array[0][i];
                if(array[0][i] < 0) array[0][i]+=Prime;
            }
        }
        for(auto &x:left) array[1].push_back((int) x-'0');
        for(auto &x:right) array[2].push_back((int) x-'0');
        Little_Gate obj;
        obj.op=op;
        obj.encode=array;
        value.push_back(obj);
    }
    //evaluate multilinear extension of W which is children nodes:
    //i is index for the pocpp_int result is the chain of multiplication store the cpp_intermediate in result need to multiply with W
    static void evaluateW(const vector<cpp_int>&points,int i, size_t depth,
        cpp_int val,vector<cpp_int>&result){
        if (depth <= 0){
            result.push_back(val);
            return;
        }
        cpp_int left= 1- points[i];
        if(left < 0) left+=Prime;
        left=(left * val) % Prime;
        evaluateW(points,i+1,depth-1,left,result);
        cpp_int right=(points[i]* val) % Prime;
        evaluateW(points,i+1,depth-1,right,result);
    }
};
//lagrange cpp_interpolation to evaluate at x for a given basis -> y's & x's -> 0,1,2
cpp_int verifier_eval_at012(vector<cpp_int>&basis,cpp_int x){
    cpp_int a= ((x-1)*(x-2) *basis[0]) / 2;
    cpp_int b= x* (2-x) * basis[1];
    cpp_int c= (x*(x-1)*basis[2]) /2;
    cpp_int out=(a+b+c)% Prime;
    return (out < 0) ? Prime+ out : out;
}
//file read and writ
class Transcript{
private:
    std::fstream file;
public:
    Transcript(std::ios_base::openmode mod){
        file.open("transcript",mod|std::ios::binary);
    }
    ~Transcript(){
        file.close();
    }
    void write_cppint(cpp_int& claim) { //transcript consist of claim of output gate followed by polynomials
        //convert in bytes 32 bit is allowed.
        vector<unsigned char> byte;
        boost::multiprecision::export_bits(claim,std::back_inserter(byte),8); //BIGENDING
        uint8_t size=byte.size(); //size can be < 32 bits
        file.write(reinterpret_cast<char*>(&size),sizeof(size));
        file.write(reinterpret_cast<char*>(byte.data()),byte.size()); //this is a fixed
    }
    void write_polynomial(vector<cpp_int>&base) {
        uint8_t size=base.size(); //since we will get polynomial evaluation of size 3 & q(x) size is no. of gate at next layer
        file.write(reinterpret_cast<char*>(&size),sizeof(uint8_t));
        for(auto &x:base) {
            write_cppint(x); //one by one writing
        }
    }
    void read_cppint(cpp_int& claim){ //reading cpp_int values
        uint8_t size;
        file.read(reinterpret_cast<char*>(&size),sizeof(size));
        vector<unsigned char>byte(size);
        file.read(reinterpret_cast<char*>(byte.data()),size);
        boost::multiprecision::import_bits(claim,byte.begin(),byte.end());
    }
    void read_polynomial(vector<cpp_int>&base) { //read polynomial
        uint8_t size;
        file.read(reinterpret_cast<char*>(&size),sizeof(uint8_t));
        base.resize(size);
        for(auto& x:base){
            read_cppint(x);
        }
    }
};
