(* Security experiment for one-time signature *)
Require Import FCF.

Section OTS.

  Variable Message : Set.
  Variable Signature : Set.
  Variable PrivateKey : Set. 
  Variable PublicKey : Set.

  Hypothesis Message_EqDec : EqDec Message.
  Hypothesis Signature_EqDec : EqDec Signature.

  Variable KeyGen : Comp (PrivateKey * PublicKey).
  Variable Sign : PrivateKey -> Message -> Comp Signature.
  Variable Verify : PublicKey -> Message -> Signature -> bool.

  (* The adversary can sign a single message *)
  Variable A_state : Set.
  Hypothesis A_state_EqDec : EqDec A_state.
  Variable A1 : PublicKey -> Comp (Message * A_state).
  Variable A2 : (Signature * A_state) -> Comp (Message * Signature).

  Variable A : PublicKey -> OracleComp Message (option Signature) (Message * Signature).
    
  (* The security of a OTS is identical to the normal definition (Signature.v)
     except that we restrict A to ask only one oracle query *) 
  Definition SingleSignOracle k state m :=
    if negb (eqb state nil) then ret (None, state) else
       sig <-$ Sign k m;
       ret (Some sig, (m::state)%list).
       
  Definition OTSigForge_G :=
    [prikey, pubkey] <-$2 KeyGen;
    [msg,state] <-$2 A1 pubkey;
    sig <-$ Sign prikey msg;
    [msg',sig'] <-$2 A2 (sig, state);
    if msg' ?= msg then ret false else ret Verify pubkey msg' sig'.
    
  Definition OTSigForge_Advantage :=
    Pr[OTSigForge_G].

  Definition OTSigForge (eps : Rat) :=
    Pr[OTSigForge_G] <= eps.
    
End OTS.   


