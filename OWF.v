(* Security experiment for one-way functions *)
Require Import FCF.

Section OWF.

  Variable Input : Set.
  Variable Output : Set.
  Variable RndInput : Comp Input. 

  Hypothesis EqDec_Input : EqDec Input.
  Hypothesis EqDec_Output : EqDec Output.
  
  (* Candidate one-way function *)
  Variable f : Input -> Output.

  (* Adversary to invert f *)
  Variable A : Output -> Comp Input.

  Definition Invert_G  :=
    x <-$ RndInput;
    x' <-$ A (f x);
    ret (f x' ?= f x).  

  Definition Invert_Advantage :=
    Pr[Invert_G].

  Definition Invert (eps : Rat) :=
    Invert_Advantage <= eps.
            
End OWF.
