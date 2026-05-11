#include "GKR.h"
//polynomial size ==3 then we are at sum-check
//polynomial size == no.of gate at next layer, we are at final step of sumcheck where verifier needs to evaluate the polynomial
//we build the circuit but only string of label since in GKR circuit structure is public input

class Labels{ //enough for verifier
private:
    static int iterator;
public:
    string label;
    shared_ptr<Labels>left;
    shared_ptr<Labels>right;
    bool witness,helper;
    OPERATOR op;
    Labels():op(NONE),witness(false),helper(false) {}
    Labels(OPERATOR op,shared_ptr<Labels>left,shared_ptr<Labels>right):witness(false),helper(false){
        this->left=left;
        this->right=right;
        this->op=op;
    }
    static void AssignLabel(Labels* root){
        std::deque<Labels*>queue;
        queue.push_back(root);
        size_t size=1;
        while(size > 0){
            shared_ptr<Labels>witness=nullptr;
            shared_ptr<Labels>helper=nullptr;
            while(size--){
                auto top=queue.front();
                queue.pop_front();
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
            vector<Labels*>values(queue.begin(),queue.end());
            iterator=0;
            assignLabel(values,"",ceil(log2(values.size())));
            size=queue.size();
        }
    }
    static shared_ptr<Labels>RecursiveBuild(std::queue<shared_ptr<Labels>>parent,shared_ptr<Labels>witness,
    shared_ptr<Labels>helper,vector<shared_ptr<Labels>>candidate)
    {
        //ADD candidate
        if(candidate.size() == 1){
            shared_ptr<Labels>node=std::make_shared<Labels>(ADD,helper,candidate[0]);
            candidate.pop_back();
            candidate.push_back(node);
        } else if(candidate.size()==2) {
            shared_ptr<Labels>node=std::make_shared<Labels>(ADD,candidate[0],candidate[1]);
            candidate.pop_back(),candidate.pop_back();
            if(parent.empty()) return node;
            candidate.push_back(node);
        }
        auto left=parent.front(); parent.pop();
        auto right=parent.front(); parent.pop();
        shared_ptr<Labels>root=std::make_shared<Labels>(ADD,left,right);
        candidate.push_back(root); //push to the add candidate
        
        std::queue<shared_ptr<Labels>>ancestor;
        while(!parent.empty()){
            auto top=parent.front();
            parent.pop();
            ancestor.push(std::make_shared<Labels>(MUL,top,witness));
        }
        if(ancestor.size() > 2) { //witness chain
            shared_ptr<Labels>node=std::make_shared<Labels>(ADD,helper,witness);
            node.get()->witness=true;
            witness=node;
        }
        if(candidate.size()==1 || ancestor.size() - 2 > 2) { //helper chain
            shared_ptr<Labels>helper_chain=std::make_shared<Labels>(ADD,helper,helper);
            helper_chain.get()->helper=true;
            helper=helper_chain;
        } 
        return RecursiveBuild(ancestor,witness,helper,candidate);  
    }
    static void Print_circuit(Labels*root){
        std::deque<Labels*>queue;
        queue.push_back(root);
        size_t size=1;
        while(size > 0){
            shared_ptr<Labels>witness=nullptr;
            shared_ptr<Labels>helper=nullptr;
            while(size--){
                auto top=queue.front();
                queue.pop_front();
                std::cout<<top->label<<",";
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
private:
    static void assignLabel(vector<Labels*>&values,string label,int depth){
        if(iterator >= values.size()) return;
        if(depth<=0){
            values[iterator]->label=label;
            iterator++;
            return;
        }
        label.push_back('0');
        assignLabel(values,label,depth-1);
        label.pop_back();
        label.push_back('1');
        assignLabel(values,label,depth-1);
        label.pop_back();
    }
};
int Labels::iterator=0;

shared_ptr<Labels>make_circuit(size_t );
vector<cpp_int> Verify(LabelInformation&,Transcript&);
vector<cpp_int> BFS(Labels*);
int main()
{
    response=0;
    int witness=5;
    vector<int>input={3,10,16,15,1,9}; // These are public inputs let's make simple circuit.
    INPUT=input;
    auto root=make_circuit(input.size());
    Labels::AssignLabel(root.get());
    Labels::Print_circuit(root.get());
    auto result=BFS(root.get());
    std::cout<<" Final gkr step:\nPoints: ";
    for(auto &x:result) std::cout<<x<<" ";
    vector<cpp_int>temp;
    temp.reserve(2+input.size());
    temp.push_back(0);
    for(auto &x:input) temp.push_back(x);
    temp.push_back(witness);
    std::cout<<'\n'<<LabelInformation::evaluateW(temp,result);
    return 0;
}

shared_ptr<Labels>make_circuit(size_t n){
    std::shared_ptr<Labels>helper=std::make_shared<Labels>();//allows same memory to address by many object without 
    std::shared_ptr<Labels>witness=std::make_shared<Labels>();//transforming the ownership.
    helper.get()->helper=true, witness.get()->witness=true;
    vector<shared_ptr<Labels>>input(n);    
    for(size_t i=0;i<n;i++) input[i]=std::make_shared<Labels>();
    std::queue<shared_ptr<Labels>>parent;//we need to pop two elements from front.
    for(size_t i=0;i<input.size();i++) {
        if( i & 1) parent.push(std::make_shared<Labels>(MUL,input[i],witness));
        else parent.push(std::make_shared<Labels>(ADD,helper,input[i]));
        input[i].reset();// release the pointer to object(ownership of inputs)
    }
    std::shared_ptr<Labels>helper_chain=std::make_shared<Labels>(ADD,helper,helper);
    shared_ptr<Labels>witness_chain=std::make_shared<Labels>(MUL,witness,witness);
    helper.reset(),witness.reset();// release 
    helper_chain.get()->helper=true,witness_chain.get()->witness=true;
    return Labels::RecursiveBuild(parent,witness_chain,helper_chain,{});
}


vector<cpp_int> Verify(LabelInformation& obj,Transcript& file) {
    int row=1,column=0; //variable index so we can have a decision of stopping the sum-check as well as bind the random-challange
    auto gate=obj.gate; //copy the label so that we can use add_gate as deriving multilinear extension
    //and gate will eventually bind to random number
    int colsize=gate[0].encode[1].size();
    for(;row <=2 ;){ //total life of sum-check
        //we verify the transcript
        vector<cpp_int>base;
        file.read_polynomial(base);
        std::cout<<"g(x) :";
        for(auto &x:base) std::cout<<x<<" , ";
        response=Circuit::verifier(base);
        if(response == -1){
            std::cerr<<"failed";
            exit(1);
        }
        std::cout<<"\nrand: "<<response << " sum-check claim: "<<claim<<std::endl;
         //binding the random 
        for(auto & c: gate){
            c.encode[row][column]=response;
        }
        column++; 
        if(column==colsize){
            row++;
            column=0;
        } 
    } //final step of sum-check
    vector<cpp_int>q ;
    file.read_polynomial(q);
    std::cout<<"q(x): ";
    for(auto &x:q) std::cout<<x<<" , ";
    cpp_int q0=LabelInformation::Reconstruct_line(q,0);
    cpp_int q1=LabelInformation::Reconstruct_line(q,1);
    std::cout<<"\nq(0)= "<<q0 <<" , q(1)= "<<q1<<std::endl;
    cpp_int sum=0;
    for(size_t i=0;i<gate.size();i++) {
        sum =sum + Circuit::finalSumCheck(q0,q1,obj.gate[i].encode,gate[i].encode,gate[i].op);
    } sum=sum% Prime;
    if(sum != claim) {
        std::cerr<<"Failed";
        exit(1);
    }
    response=verifier_message(q); //r*
    claim=LabelInformation::Reconstruct_line(q,response); //claim is reduced to next layer
    std::cout<<"Next layer claim: "<<claim <<" r*: "<<response<<"\n\n";
    return LabelInformation::Line(gate[0].encode[1],gate[0].encode[2],response);
}


vector<cpp_int> BFS(Labels* root){
    std::deque<Labels*> queue;
    queue.push_back(root);
    size_t size=1;
    Transcript file(std::ios::in);
    file.read_cppint(claim);
    std::cout<<"Claimed value of Output gate: "<<claim<<std::endl;
    vector<cpp_int>current;//the current gate label is bind to random value at first
    while(size > 0) {
        //verifier can evaluate at her own at leaf node.
        if(queue.front()->op==NONE) break;
        LabelInformation obj;
        shared_ptr<Labels>witness=nullptr;
        shared_ptr<Labels>helper=nullptr;
        while(size--){ // iteration layer by layer
            auto top=queue.front();
            queue.pop_front();
            switch(top->op) {
                case ADD:
                    obj.init(current,top->left.get()->label,top->right.get()->label,top->label,top->op);
                    break;
                case MUL:
                    obj.init(current,top->left.get()->label,top->right.get()->label,top->label,top->op);
                    break;
                case NONE: //leaf 
                    break;
            };
            if(top->left) {
                if(top->left.get()->witness) continue;
                if(top->left.get()->helper) helper=top->left;
                else queue.push_back(top->left.get());
            }
            if(top->right){
                if(top->right.get()->helper) continue;
                if(top->right.get()->witness) witness=top->right;
                else queue.push_back(top->right.get());
            }//Wi(r) takes wi+1(r)
        }std::cout<<std::endl; //after this we will use sum-check protocol
        if(helper){
            queue.push_front(helper.get());
        }
        if(witness){
            queue.push_back(witness.get());
        }
        current = Verify(obj,file);
        size=queue.size();
    }
    return current;
}