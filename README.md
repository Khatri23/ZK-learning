You can find the documentation on the design of an n-degree polynomial to arithmetic circuit.
The motivation behind this project is to help readers build clarity on implementing the GKR protocol from first principles.
This is written entirely based on my own understanding.
Fiat shamir transformation is relatively simple, you just need to replace verifier message with cryptographic hash function.
The folder Fiat-Shamir contains the FSprover and FSverifier where prover sends the transcript basically the prover message and 
claim value. The verifier simply verify the transcript under the some constraint 
