// We render the protocol as non-interactive via fiat shamir
//so we can remove the verifier part completely from program.
//we need a hash-function that replaces verifier message where we query our input to hash to get fixed output basically ROM
//prover send the transcript so we will use file handling to simulate the process.
#include"GKR.h"
shared_ptr<Node> makeCircuit(const vector<int>&,const int&);
void Print_circuit(Node*root){
    std::deque<Node*>queue;
    queue.push_back(root);
    size_t size=1;
    while(size > 0){
        shared_ptr<Node>witness=nullptr;
        shared_ptr<Node>helper=nullptr;
        while(size--){
            auto top=queue.front();
            queue.pop_front();
            std::cout<<top->value<<": " <<top->label<<",";
            if(top->left) {
                if(top->left.get()->witness) continue;
                if(top->left.get()->helper) helper=top->left;
                else queue.push_back(top->left.get());
            }
            if(top->right){
                if(top->right.get()->helper) continue;
                if(top->right.get()->witness) witness=top->right;
                else queue.push_back(top->right.get());
            }
        }
        if(helper) queue.push_front(helper.get());
        if(witness) queue.push_back(witness.get());
        size=queue.size();
        std::cout<<std::endl;
    }
}
int main()
{
    response=0;
    int witness=5;
    vector<int>input={3,10,16,15,1,9};
    INPUT=input;
    shared_ptr<Node>root=makeCircuit(input,witness);
    Circuit::AssignLabel(root.get());
    Print_circuit(root.get());
    BFS(root.get());
   //verifier can check in her own
   //let's assume prover sends the witness along side.
   vector<int>temp;
    return 0;
}

shared_ptr<Node> makeCircuit(const vector<int>&x,const int& w)
{
    std::shared_ptr<Node>helper=std::make_shared<Node>(0);//allows same memory to address by many object without 
    std::shared_ptr<Node>witness=std::make_shared<Node>(w);//transforming the ownership.
    helper.get()->helper=true, witness.get()->witness=true;
    vector<shared_ptr<Node>>input(x.size());    
    for(size_t i=0;i<x.size();i++) input[i]=std::make_shared<Node>(x[i]);
    std::queue<shared_ptr<Node>>parent;//we need to pop two elements from front.
    for(size_t i=0;i<input.size();i++) {
        if( i & 1) parent.push(std::make_shared<Node>(MUL,input[i],witness));
        else parent.push(std::make_shared<Node>(ADD,helper,input[i]));
        input[i].reset();// release the pointer to object(ownership of inputs)
    }
    std::shared_ptr<Node>helper_chain=std::make_shared<Node>(ADD,helper,helper);
    shared_ptr<Node>witness_chain=std::make_shared<Node>(MUL,witness,witness);
    helper.reset(),witness.reset();// release 
    helper_chain.get()->helper=true,witness_chain.get()->witness=true;
    return Circuit::RecursiveBuild(parent,witness_chain,helper_chain,{});
}

