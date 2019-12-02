# lamportOTS
Formally verified proof for Lamport's one-time signature scheme (https://en.wikipedia.org/wiki/Lamport_signature) using the Foundational Cryptography Framework (https://github.com/adampetcher/fcf). 

To my knowledge, this is the only formally verified proof of this well-known scheme. 

OWF.v : security definitions for a one-way function
OTS.v : security definitions for a one-time signature scheme
LamportScheme.v : model of Lamport's one-time signature scheme with a correctness proof
LamportProof.v : formal proof that the model in LamportScheme.v is unforgeable based on the definition in OTS.v. This proof is in the sequence-of-games style. 
IndepAnd.v : interesting auxiliary proof of a useful probability theorem done by Adam Petcher 
