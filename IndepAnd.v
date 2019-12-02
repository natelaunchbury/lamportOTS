(* Done by Adam Petcher with Nate Launchbury *)

Require Import FCF.

Theorem indep_and:
  forall (ca cb : Comp bool),
  Pr[x <-$ ca; y <-$ cb; ret (x && y)] == Pr[ca] * Pr[cb].

  pose proof getSupport_NoDup.
  intros.
  simpl.

  (* "destruct a" *)
  destruct (In_dec (EqDec_dec _) true (getSupport ca)).
  (* if a is the only non-zero value in the support then 
       sumList ls f = f a  
   *)
  - rewrite (@sumList_exactly_one _ true); trivial.
    (* first var is true *) 
    + destruct (In_dec (EqDec_dec _) true (getSupport cb)).
      rewrite (@sumList_exactly_one _ true); trivial.
      simpl.
      fcf_compute.
        * intros.
        fcf_compute.
      
        (* "divide" by Pr[ca] on both sides *)
        * eapply ratMult_eqRat_compat; try reflexivity.
        simpl.
        eapply eqRat_trans.
        (* by hyp n, the support of cb is empty *)
        apply sumList_0.
        intros.
        fcf_compute.
        symmetry.
        apply getSupport_not_In_evalDist.
        trivial.

    (* first var is false *) 
    + intros.
    destruct b; intuition. 
    simpl.
    eapply eqRat_trans.
    apply ratMult_eqRat_compat.
    reflexivity.
    apply sumList_0.
    intros.
    fcf_compute.
    fcf_compute.

  (* support of ca is empty *)
  - eapply eqRat_trans.
    + eapply sumList_0.
    intros.
    destruct a; intuition.
    simpl.
    eapply eqRat_trans.
      * eapply ratMult_eqRat_compat; [reflexivity | idtac].
        eapply sumList_0.
        intros.
        fcf_compute.
      * apply ratMult_0_r.
    
    + symmetry.
      eapply eqRat_trans.
      * apply ratMult_eqRat_compat; [
        apply getSupport_not_In_evalDist;trivial | 
        reflexivity].
      * apply ratMult_0_l.

Qed.


