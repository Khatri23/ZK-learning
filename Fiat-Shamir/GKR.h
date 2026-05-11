 #ifndef GKR
#include"util.h"
#include<queue>
static cpp_int claim; //tracks the claims where verifier checks based on prover response.
static cpp_int response;
vector<int>INPUT;

#include<openssl/evp.h>
// verifier msg-> h(x,c_i-1,r_i-1,g_i)
cpp_int verifier_message(vector<cpp_int>&g) { 
    EVP_MD_CTX * ctx= EVP_MD_CTX_new();
    EVP_DigestInit_ex(ctx,EVP_sha256(),nullptr);
    vector<unsigned char> byte;
    byte.reserve(INPUT.size()*4+8+g.size()*4); //converting all info to byte assuming 32 bit environment
    for(auto &x:INPUT){
        byte.push_back((x >> 24)& 0xff), byte.push_back((x >> 16) & 0xff);
        byte.push_back((x >> 8)& 0xff), byte.push_back(x & 0xff);
    }
    byte.push_back(((claim >> 24) & 0xff).convert_to<unsigned char>()), byte.push_back(((claim >> 16)& 0xff).convert_to<unsigned char>());
    byte.push_back(((claim >> 8)& 0xff).convert_to<unsigned char>()), byte.push_back((claim & 0xff).convert_to<unsigned char>()); 
    byte.push_back(((response >> 24) & 0xff).convert_to<unsigned char>()), byte.push_back(((response >> 16)& 0xff).convert_to<unsigned char>());
    byte.push_back(((response >> 8)& 0xff).convert_to<unsigned char>()), byte.push_back((response & 0xff).convert_to<unsigned char>()); 
    for(auto &x:g){
        byte.push_back(((x >> 24) & 0xff).convert_to<unsigned char>()), byte.push_back(((x >> 16)& 0xff).convert_to<unsigned char>());
        byte.push_back(((x >> 8)& 0xff).convert_to<unsigned char>()), byte.push_back((x & 0xff).convert_to<unsigned char>());
    }
    
    if(EVP_DigestUpdate(ctx,byte.data(),byte.size())!=1){
        std::cerr<<"Failed to update digest";
        EVP_MD_CTX_free(ctx);
        exit(1);
    }
    unsigned char hash[32];
    EVP_DigestFinal(ctx,hash,nullptr);
    cpp_int result; 
    boost::multiprecision::import_bits(result,hash,hash+4); //first 32 bit
    EVP_MD_CTX_free(ctx);
    return result %Prime;
}
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
    //build the tree from make circuit
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
    //except from the last step of sum check verifier just evaluate at f1(r)=f2(0) & f2(1)
    static cpp_int verifier(vector<cpp_int>&basis){ //-1 for fail other wise send the random value.
        cpp_int v=verifier_eval_at012(basis,0)+verifier_eval_at012(basis,1);
        if( v >= Prime) v-=Prime;
        if(v != claim) return -1;//claim is false
        //choose the random and set the next claim:
        cpp_int r=verifier_message(basis);
        claim=verifier_eval_at012(basis,r);
        return r; //send random value
    }

    static cpp_int EvaluateGate(vector<vector<cpp_int>>obj,const int& row,const int& column,const cpp_int& x,
    const vector<cpp_int>& W, OPERATOR op,const vector<vector<cpp_int>>&orignal) {
        //instead of polynomial we send lagrange basis evaluation at x so:
        //we need original obj value to decide the structure of multilinear extension for add & mult
        vector<cpp_int>view=orignal[1]; //original view such that we can construct multilinear extension
        cpp_int v=1;
        for(auto &x:orignal[0]) v=(v*x)%Prime;
        for(auto & x: orignal[2]) view.push_back(x);
        vector<cpp_int>points;
        obj[row][column]=x;
        for(auto & x: obj[1]) points.push_back(x);
        for(auto &x: obj[2]) points.push_back(x);

        cpp_int w1=LabelInformation::evaluateW(W,obj[1]);
        cpp_int w2=LabelInformation::evaluateW(W,obj[2]);
        cpp_int w;
        if(op==ADD){
            w=w1+w2;
            if(w > Prime) w-=Prime;
        } else if(op==MUL){
            w=(w1*w2) % Prime;
        }
        return (OPEval(view,points,v)*w) % Prime;
    }
    //verifier calls this to evaluate f using q(0) & q(1)
    static cpp_int finalSumCheck(const cpp_int& q0,const cpp_int& q1,const vector<vector<cpp_int>>&original,
        const vector<vector<cpp_int>>&obj, OPERATOR op){
        vector<cpp_int>view=original[1]; //original view such that we can construct multilinear extension
        cpp_int v=1;
        for(auto &x:original[0]) v=(v*x)%Prime;     
        for(auto & x: original[2]) view.push_back(x);
        vector<cpp_int>points;
        for(auto & x: obj[1]) points.push_back(x);
        for(auto &x: obj[2]) points.push_back(x);

        cpp_int w;
        if(op==ADD) w=q0+q1;
        else w=q0*q1;
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
    static cpp_int OPEval(vector<cpp_int>& view,vector<cpp_int>& points,cpp_int & result){
        cpp_int y;
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



vector<cpp_int> SumCheck(LabelInformation& obj,Transcript& file)
{
    int row=1,column=0; //variable index so we can have a decision of stopping the sum-check as well as bind the random-challange
    auto gate=obj.gate;
    int colsize=gate[0].encode[1].size();
    for(;row <=2 ;){ //total life of sum-check
        vector<cpp_int>basis;
        basis.reserve(3);
        for(int x=0;x <3 ;x++){ // evaluation at 0,1,2
            cpp_int sum=0;
            for(size_t current=0;current<gate.size();current++){ //extract each gate at that layer
                sum+=Circuit::EvaluateGate(gate[current].encode,row,column,x,obj.W,gate[current].op,
                    obj.gate[current].encode);
                if( sum >= Prime) sum-=Prime;
            }
            basis.push_back(sum);
        } // prover work done .
        std::cout<<"Prover: " <<basis[0]<< ", "<<basis[1]<<", "<<basis[2] << std::endl;
        file.write_polynomial(basis);
        response=verifier_message(basis);
        claim=verifier_eval_at012(basis,response);//next claim
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
    vector<cpp_int>q;
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
    file.write_polynomial(q);
    response=verifier_message(q);//r*
    claim=LabelInformation::Reconstruct_line(q,response); //claim is reduced to next layer
    std::cout<<"\nNext claim= "<<claim<<" r* "<<response<<std::endl;
    return LabelInformation::Line(gate[0].encode[1],gate[0].encode[2],response);
}

void BFS(Node* root){
    std::deque<Node*> queue;
    queue.push_back(root);
    size_t size=1;
    claim=root->value;
    Transcript file(std::ios::out);
    std::cout<<"Claimed value of Output gate: "<<claim<<std::endl;
    vector<cpp_int>current;//the current gate label is bind to random value at first
    file.write_cppint(claim);
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
        current = SumCheck(obj,file);
        size=queue.size();
    }
}

#endif