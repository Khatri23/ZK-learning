#include<iostream>
struct Node{
    Node * next;
    int data;
    Node(int data){
        this->data = data;
        next = nullptr;
    }
};
//insertion at head
Node * insert_head(Node* head, int data){
    if(head==nullptr){
        return new Node(data);
    }
    Node* current = new Node(data);
    current->next= head;
    return current;
}
//insert in between
Node* insert(Node* head, int data, int pos) {
    if(head == nullptr) return new Node(data);
    Node* current = new Node(data);
    Node * prev = nullptr,*temp=head;
    while(pos-- && temp!=nullptr){
        prev= temp;
        temp=temp->next;
    }
    prev->next=current,current->next= temp;
    return head;
}
Node * Delete(Node* head,int pos) {
    if(head == nullptr) return nullptr;
    Node * temp=head,*prev=head;
    while(--pos && temp!=nullptr) {
        prev=temp;
        temp=temp->next;
    }//require to delete temp.
    Node* current=nullptr;
    if(temp== head) {
        current = head;
        head= head->next;
    } else {
        current = temp;
        prev->next =(temp)? temp->next:nullptr;
    }
    free(current);
    return head;
}
int main() {
    Node* head = new Node(1);
    Node* temp = head;
    for(int i=2;i<=5;i++) {
        Node* current = new Node(i);
        temp->next= current;
        temp=current;
    }
    head= insert_head(head,0);
    head= Delete(head,68);
    temp = head;
    while(temp!= nullptr) {
        Node* current = temp;
        temp=temp->next;
        std::cout<<current->data<<std::endl;
        free(current);
    }
    return 0;
}