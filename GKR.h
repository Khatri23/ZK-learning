 #ifndef GKR
#include"util.h"
#include<random>
static int claim; //tracks the claims where verifier checks based on prover response.
std::random_device rd;
std::mt19937 gen(rd());
std::uniform_int_distribution<int>dis(1,Prime-1);

//necessary functions for circuit
class Circuit {
private:
    static int iterator;
public :
     static void AssignLabel(Node* root){
        std::deque<Node*>queue;
        queue.push_back(root);
        size_t size=1;
        while(size > 0){
            shared_ptr<Node>witness=nullptr;
            shared_ptr<Node>helper=nullptr;
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
            vector<Node*>values(queue.begin(),queue.end());
            iterator=0;
            assignLabel(values,"",ceil(log2(values.size())));
            size=queue.size();
        }
    }
    //build the tree from bottom up to  make circuit
    static shared_ptr<Node>RecursiveBuild(std::queue<shared_ptr<Node>>parent,shared_ptr<Node>witness,
    shared_ptr<Node>helper,vector<shared_ptr<Node>>candidate)
    {
        //ADD candidate
        if(candidate.size() == 1){
            shared_ptr<Node>node=std::make_shared<Node>(ADD,helper,candidate[0]);
            candidate.pop_back();
            candidate.push_back(node);
        } else if(candidate.size()==2) {
            shared_ptr<Node>node=std::make_shared<Node>(ADD,candidate[0],candidate[1]);
            candidate.pop_back(),candidate.pop_back();
            if(parent.empty()) return node;
            candidate.push_back(node);
        }
        auto left=parent.front(); parent.pop();
        auto right=parent.front(); parent.pop();
        shared_ptr<Node>root=std::make_shared<Node>(ADD,left,right);
        candidate.push_back(root); //push to the add candidate
        
        std::queue<shared_ptr<Node>>ancestor;
        while(!parent.empty()){
            auto top=parent.front();
            parent.pop();
            ancestor.push(std::make_shared<Node>(MUL,top,witness));
        }
        if(ancestor.size() > 2) { //witness chain
            shared_ptr<Node>node=std::make_shared<Node>(ADD,helper,witness);
            node.get()->witness=true;
            witness=node;
        }
        if(candidate.size()==1 || ancestor.size() - 2 > 2) { //helper chain
            shared_ptr<Node>helper_chain=std::make_shared<Node>(ADD,helper,helper);
            helper_chain.get()->helper=true;
            helper=helper_chain;
        } 
        return RecursiveBuild(ancestor,witness,helper,candidate);  
    }
    //except from the last step of sum check verifier just evaluate at f1(r)=?f2(0)+f2(1)
    static int verifier(vector<int>&basis){ //-1 for fail other wise send the random value.
        int v=verifier_eval_at012(basis,0)+verifier_eval_at012(basis,1);
        if( v >= Prime) v-=Prime;
        if(v != claim) return -1;//claim is false
        //choose the random and set the next claim:
        int r=dis(gen);
        claim=verifier_eval_at012(basis,r);
        return r; //send random value
    }

    static int EvaluateGate(vector<vector<int>>obj,const int& row,const int& column,const int& x,
    const vector<int>& W, OPERATOR op,const vector<vector<int>>&orignal) {
        //instead of polynomial we send lagrange basis evaluation at x so:
        //we need original obj value to decide the structure of multilinear extension for add & mult
        vector<int>view=orignal[1]; //original view such that we can construct multilinear extension
        int v=1;
        for(auto &x:orignal[0]) v=(v*x)%Prime;
        for(auto & x: orignal[2]) view.push_back(x);
        vector<int>points;
        obj[row][column]=x;
        for(auto & x: obj[1]) points.push_back(x);
        for(auto &x: obj[2]) points.push_back(x);

        int w1=LabelInformation::evaluateW(W,obj[1]);
        int w2=LabelInformation::evaluateW(W,obj[2]);
        int w;
        if(op==ADD){
            w=w1+w2;
            if(w > Prime) w-=Prime;
        } else if(op==MUL){
            w=(w1*w2) % Prime;
        }
        return (OPEval(view,points,v)*w) % Prime;
    }
    //verifier calls this to evaluate f using q(0) & q(1)
    static int finalSumCheck(const int& q0,const int& q1,const vector<vector<int>>&original,
        const vector<vector<int>>&obj, OPERATOR op){
        vector<int>view=original[1]; //original view such that we can construct multilinear extension
        int v=1;
        for(auto &x:original[0]) v=(v*x)%Prime;     
        for(auto & x: original[2]) view.push_back(x);
        vector<int>points;
        for(auto & x: obj[1]) points.push_back(x);
        for(auto &x: obj[2]) points.push_back(x);

        int w= (op==ADD)? q0+q1 : q0*q1;
        w=w % Prime;
        return (OPEval(view,points,v) * w) % Prime;
    }
private:
    static void assignLabel(vector<Node*>&values,string label,int depth){
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
    //evaluate the multilinear extension of ADD & MULT
    static int OPEval(vector<int>& view,vector<int>& points,int & result){
        int y;
        for(size_t i=0;i<view.size();i++){
            if(view[i]==0) {
              y=1- points[i];
              if(y < 0) y+=Prime;  
            } else{
                y=points[i];
            }
            result=(result * y)%Prime;
        }
        return result;
    }
};
int Circuit::iterator=0;

vector<int> SumCheck(LabelInformation& obj)
{
    int row=1,column=0; //variable index so we can have a decision of stopping the sum-check as well as bind the random-challange
    auto gate=obj.gate;
    int colsize=gate[0].encode[1].size();
    for(;row <=2 ;){ //total life of sum-check
        vector<int>basis;
        basis.reserve(3);
        for(int x=0;x <3 ;x++){ // evaluation at 0,1,2
            int sum=0;
            for(size_t current=0;current<gate.size();current++){ //extract each gate at that layer
                sum+=Circuit::EvaluateGate(gate[current].encode,row,column,x,obj.W,gate[current].op,
                    obj.gate[current].encode);
                if( sum >= Prime) sum-=Prime;
            }
            basis.push_back(sum);
        } // prover work done .
        std::cout<<"Prover: " <<basis[0]<< ", "<<basis[1]<<", "<<basis[2] << std::endl;
        std::cout<<"Verifier ";//verifier
        auto response=Circuit::verifier(basis);
        if(response==-1){
            std::cout<<" Failed";
            exit(-1);
        } std::cout<<"rand: "<<response<<" g(r)= "<<claim<<std::endl;
        //binding the random 
        for(auto & c: gate){
            c.encode[row][column]=response;
        }
        column++; 
        if(column==colsize){
            row++;
            column=0;
        }   
    }
    //at this point the verifier needs to verify the f but cannot on her own so both verifier & prover agree on line 
    //prover sends q(x) of degree at most log(n) which is gate at next layer. l(0)=gate[0][1] & l(1)=gate[0][2]
    vector<int>q;
    q.reserve(gate[0].encode[1].size()+1);//again we will send lagrange basis so for k -degree we need k+1 basis.
    std::cout<<"bind: ";
    for(auto &x:gate[0].encode[1]) std::cout<<x<<" "; 
    for(auto &x:gate[0].encode[2]) std::cout<<x<<" ";
    std::cout<<std::endl;
    for(size_t i=0;i <= gate[0].encode[1].size();i++){ 
        auto points=LabelInformation::Line(gate[0].encode[1],gate[0].encode[2],Prime-1-i);
        for(auto &x:points) std::cout<<x<<" ";
        std::cout<<std::endl;
        q.push_back(LabelInformation::evaluateW(obj.W,points));
    } std::cout<<"q(x) = ";
    for(auto &x:q) std::cout <<x<<" ";
    //verifier can use q(0) , q(1) to evaluate the f
    int q0=LabelInformation::Reconstruct_line(q,0),q1=LabelInformation::Reconstruct_line(q,1);
    int sum=0;
    for(size_t i=0;i< gate.size();i++){
        sum =sum + Circuit::finalSumCheck(q0,q1,obj.gate[i].encode,gate[i].encode,obj.gate[i].op);
    } sum= sum % Prime;
    if(sum != claim) {
        std::cerr<<"Failed to verify";
        exit(1);
    } //verifier is convinced that q(0)=W(l) and q(1)=W(r) : l,r are child label.
    int r=dis(gen); //chooses random point
    claim=LabelInformation::Reconstruct_line(q,r); //claim is reduced to next layer
    std::cout<<"\nNext claim= "<<claim<<" r* "<<r<<std::endl;
    return LabelInformation::Line(gate[0].encode[1],gate[0].encode[2],r);
}
vector<int> BFS(Node* root){
    std::deque<Node*> queue;
    queue.push_back(root);
    size_t size=1;
    claim=root->value;
    std::cout<<"Claimed value of Output gate: "<<claim<<std::endl;
    vector<int>current;//the current gate label is bind to random value at first
    while(size > 0) {
        //verifier can evaluate at her own at leaf node.
        if(queue.front()->op==NONE) break;
        LabelInformation obj;
        shared_ptr<Node>witness=nullptr;
        shared_ptr<Node>helper=nullptr;
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
                else{
                    queue.push_back(top->left.get());
                    obj.W.push_back(top->left.get()->value);
                }
            }
            if(top->right){
                if(top->right.get()->helper) continue;
                if(top->right.get()->witness) witness=top->right;
                else{
                    queue.push_back(top->right.get());
                    obj.W.push_back(top->right.get()->value);
                }
            }//Wi(r) takes wi+1(r)
        }std::cout<<std::endl; //after this we will use sum-check protocol
        if(helper){
            queue.push_front(helper.get());
            obj.W.insert(obj.W.begin(),helper.get()->value);
        }
        if(witness){
            queue.push_back(witness.get());
            obj.W.push_back(witness.get()->value);
        }
        current = SumCheck(obj);
        getchar();
        size=queue.size();
    }
    return current;
}

#endif