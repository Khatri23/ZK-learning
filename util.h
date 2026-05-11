#pragma once
#include<iostream>
#include<vector>
#include<memory>
#include<queue>
using std::string,std::vector,std::shared_ptr;
using std::make_shared;
#define Prime 67
//Information of a node in tree of fan-in 2
enum OPERATOR{ADD,MUL,NONE};
class Node{
public:
    int value;
    string label;
    shared_ptr<Node>left;
    shared_ptr<Node>right;
    OPERATOR op;
    bool helper,witness;
    Node(){}
    Node(int value):op(NONE),helper(false),witness(false){
        this->value=value;
    }
    Node(OPERATOR op,shared_ptr<Node>left,shared_ptr<Node>right)
    :helper(false),witness(false){
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

int multiplicative_inverse(const int& a) {
    int u=a,v= Prime;
    int x1=1,x2=0;
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
    int result;
    if (u == 1) result= x1 % Prime;
    else result= x2 % Prime;
    if(result < 0) result+=Prime;
    return result;
}
#include<cmath>

struct Little_Gate{
    vector<vector<int>>encode; //encodes parent, child
    OPERATOR op;
};
//we iterate label by label so we need to care about the gate value ADD, MULT -> its wiring predicate
// we also need to define the multilinear extension for gate value
class LabelInformation{
public:
    vector<Little_Gate>gate;//this will encode the current gate label & its neighbours
    vector<int>W;//function mapping {0,1}^k -> F where k is power of 2 since the total gate in each layer is 2^k
    LabelInformation(){}
    void init(const vector<int>& parent, string& left,string& right,string & current,OPERATOR op){
        Look_operator(gate,parent,left,right,current,op);
    }
    //return's W(points)
    static int evaluateW(const vector<int>& W, const vector<int>points) {
        //W is array of gate value at layer i.
        vector<int>intermedies;
        intermedies.reserve(W.size()); //points size is equal to the label which is no. of variables
        evaluateW(points,0,points.size(),1,intermedies);
        int result=0;
        for(size_t i=0;i<W.size();i++){
            result=(result + W[i]*intermedies[i])% Prime;
        }
        return result;
    }
    //defines the l(x) from random values again this returns the evaluation at p-1,p-2,... which is plug into W to send to verifier 
    static vector<int>Line(const vector<int>& l0,const vector<int>& l1,int x) {
        vector<int>points;
        points.reserve(l1.size());
        for(size_t i=0;i<l0.size();i++){
            int y= ((1-x)*l0[i] + x*l1[i])%Prime;
            if(y < 0) y+=Prime;
            points.push_back(y);
        }
        return points;
    }
    //lagrange interpolation for the line which evaluate directly constructing the polynomial at val
    static int Reconstruct_line(const vector<int>&basis, int val) {
        vector<int>x;
        x.reserve(basis.size());
        for(size_t i=0;i < basis.size();i++) {
            x.push_back(Prime-1-i); // 18,17... size varies based on layer
        }
        int sum=0;
        for(size_t i=0;i<x.size();i++){
            int numerator=basis[i],denominator=1;
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
    void Look_operator(vector<Little_Gate>&value,const vector<int> parent, string& left,
        string& right,string& current,OPERATOR op){
        vector<vector<int>>array(3);//label of current and its child
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
    //i is index for the point result is the chain of multiplication store the intermediate in result need to multiply with W
    static void evaluateW(const vector<int>&points,int i, int depth,
        int val,vector<int>&result){
        if (depth <= 0){
            result.push_back(val);
            return;
        }
        int left= 1- points[i];
        if(left < 0) left+=Prime;
        left=(left * val) % Prime;
        evaluateW(points,i+1,depth-1,left,result);
        int right=(points[i]* val) % Prime;
        evaluateW(points,i+1,depth-1,right,result);
    }
};
//lagrange interpolation to evaluate at x for a given y's & x's -> 0,1,2
int verifier_eval_at012(vector<int>&basis,int x){
    int a= ((x-1)*(x-2) *basis[0]) / 2;
    int b= x* (2-x) * basis[1];
    int c= (x*(x-1)*basis[2]) /2;
    int out=(a+b+c)% Prime;
    return (out < 0) ? Prime+ out : out;
}



