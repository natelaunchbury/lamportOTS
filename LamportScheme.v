
(* Lamport's one-time signature *)

Require Import FCF.
Require Import Bvector.
Require Import OTS.
Require Import OWF.
Require ZArith.



Section LamportScheme.


(*  ------------------------- Scheme ------------------------- *)

  (* Security is based on the assumption of a one-way function H *)
  Variable H : forall n, (Bvector n) -> (Bvector n).


  (* Key generation builds a 2xl matrix out of random (Bvector n)'s *)
  Fixpoint OTSKeyGen_priv (n l : nat) :=
    match l with
    | 0 => ret (nil,nil)
    | S l' =>  x0 <-$ {0,1}^n;
               x1 <-$ {0,1}^n;
               [xi0,xi1] <-$2 OTSKeyGen_priv n l';
               ret ((x0::xi0)%list,(x1::xi1)%list)
    end.
 
  Definition OTSKeyGen (n l : nat) : Comp ((list (Bvector n) * list (Bvector n)) * (list (Bvector n) * list (Bvector n))) := 
    [xi0,xi1] <-$2 OTSKeyGen_priv n l;
    ret ((xi0,xi1),(map (H n) xi0, map (H n) xi1)).
       



  (* To Sign a message you return the corresponding bits of xib *) 
  Fixpoint OTSSign {n l : nat} (prikey : (list (Bvector n) * list (Bvector n)))
           (msg : Bvector l) : Comp (list (Bvector n)) := 
    match msg with
    | Vector.nil _ => ret nil
    | Vector.cons _ b _ msg' =>  
      match prikey with
      | ((x0::xi0)%list,(x1::xi1)%list) =>
          sig <-$ OTSSign (xi0,xi1) msg';
          if b then ret (x1 :: sig)%list
               else ret (x0 :: sig)%list
      | _ => ret nil
      end
    end.

   (* To Verify you check that "map" H s = "path" of m through pubkey  *)
   (* i.e. s is the correponding Bvectors from the prikey              *)
  Fixpoint OTSVerify {n l : nat} (pubkey : (list (Bvector n) * list (Bvector n)))
                     (msg : Bvector l) (sig : list (Bvector n)) : bool := 
    match (pubkey, sig, msg) with
    | ((nil,nil),nil,Vector.nil _) => true
    | (((y0::yi0)%list,(y1::yi1)%list),(s::sig')%list,(Vector.cons _ b _ msg'))=>
          ((if b then y1 else y0) ?= (H n s)) && OTSVerify (yi0,yi1) msg' sig'
    | _ => false
    end.

  Lemma well_formed_OTSSign : forall l n msg prikey, 
    well_formed_comp (@OTSSign n l prikey msg).
  Proof.
    induction l; intuition.
    unfold Bvector in msg.       
    assert (msg = []).
    apply vector_0.
    subst.
    simpl; wftac.


    assert (exists m ms, msg = m::ms).
    apply vector_S.
    inversion H0.
    inversion H1.
    subst.
    simpl.
    destruct a; wftac.
    destruct b; wftac.
    Qed.






(*  ------------------------- Correctness ------------------------ *)

  Ltac inv H := (inversion H; subst; clear H).


  Lemma OTS_keygen_keylengths : forall n l xi0 xi1 yi0 yi1,
      In ((xi0,xi1),(yi0,yi1)) (getSupport (OTSKeyGen n l)) ->
      length xi0 = length yi0 /\ length xi1 = length yi1.
  Proof.
    intros.
    unfold OTSKeyGen in H0.
    simp_in_support;
    destruct x;
    simpl in H2;
    inversion H2;
    inversion H0;
    rewrite map_length;
    reflexivity;

    apply except;
    assumption.
  Qed.    

  (* APT *)
  Lemma OTS_keygen_keylengths2 : forall n l xi0 xi1 yi0 yi1,
      In ((xi0,xi1),(yi0,yi1)) (getSupport (OTSKeyGen n l)) ->
      length xi0 = l /\ length xi1 = l.
  Proof. 
    induction l; intros.
    - unfold OTSKeyGen, OTSKeyGen_priv in H0.
      simpl in H0.
      destruct H0.
      inv H0.
      auto.
      exfalso.
      auto.
    - unfold OTSKeyGen, OTSKeyGen_priv in H0.
      repeat simp_in_support;
      fold OTSKeyGen_priv in H4.
      + destruct x2.
        repeat simp_in_support.
        edestruct IHl.
        unfold OTSKeyGen.
        eapply getSupport_In_Seq.
        eauto.
        simpl.
        eauto.
        simpl.
        omega.

      + destruct x2.
        repeat simp_in_support.
        edestruct IHl.
        unfold OTSKeyGen.
        eapply getSupport_In_Seq.
        eauto.
        simpl.
        eauto.
        simpl.
        omega.
  Qed.

  Lemma OTS_keygenpriv_keylengths : forall l n xi0 xi1,
      In (xi0,xi1) (getSupport (OTSKeyGen_priv n l)) ->
      length xi0 = l /\ length xi1 = l.
  Proof.
    induction l; intros.
    - unfold OTSKeyGen_priv in H0.
      repeat simp_in_support.
      simpl.
      split; reflexivity.
    - unfold OTSKeyGen_priv in H0.
      fold OTSKeyGen_priv in H0.
      repeat simp_in_support;
      destruct x1.
      simp_in_support.
      simpl.
      f_equal.
      assert (length l0 = l /\ length l1 = l).
      eapply IHl.
      try eassumption.
      inversion H0.
      try assumption.
      
      simp_in_support.
      simpl.
      f_equal.
      eapply IHl.
      eassumption.
  Qed.


  Lemma getSupport_In_ident : forall n x,
      In x (getSupport ({0,1}^n)) ->
      In x (getSupport (x0 <-$ {0,1}^n; ret x0)).
  Proof.
    intros.
    destruct x eqn:?.
    simpl in *.
    assumption.

    pose proof getSupport_In_Seq. 
    apply (H1 _ _ (Rnd (S n)) _ (Vector.cons bool h n b) _ H0).
    simpl.
    auto.
  Qed.        

  Lemma OTS_keygen_priv_pub : forall n l k0 k1 ki0 ki1 j0 j1 ji0 ji1, 
      In (((k0::ki0)%list, (k1::ki1)%list),((j0::ji0)%list,(j1::ji1)%list)) (getSupport (OTSKeyGen n l)) ->
      (H n k0 = j0) /\ (H n k1 = j1). 
  Proof.  
    intros.
    unfold OTSKeyGen in H0.
    simp_in_support.
   
    destruct x eqn:?.
    simp_in_support.
    inversion H5.
    reflexivity.

    destruct x eqn:?.
    simp_in_support.
    inversion H6.
    reflexivity.
  Qed.


  Lemma OTS_keygen_priv_pub_l : forall n l ki0 ki1 ji0 ji1,
      In (ki0,ki1, (ji0,ji1)) (getSupport (OTSKeyGen n l)) ->
      ji0 = map (H n) ki0.
  Proof.
    intros.
    unfold OTSKeyGen in H0.
    simp_in_support.
    destruct x.
    simp_in_support.
    reflexivity.
  Qed.

  Lemma OTS_keygen_priv_pub_r : forall n l ki0 ki1 ji0 ji1,
      In (ki0,ki1, (ji0,ji1)) (getSupport (OTSKeyGen n l)) ->
      ji1 = map (H n) ki1.
  Proof.
    intros.
    unfold OTSKeyGen in H0.
    simp_in_support.
    destruct x.
    simp_in_support.
    reflexivity.
  Qed.


  (* Quite a strong result *)
  Lemma OTS_keygen_priv_uniform : forall l n xi0 xi1,
      length xi0 = l -> length xi1 = l ->
      In (xi0,xi1) (getSupport (OTSKeyGen_priv n l)).
  Proof.
    induction l; intros.
     - unfold OTSKeyGen_priv.
       simpl.
       left.
       apply length_zero_iff_nil in H0.
       apply length_zero_iff_nil in H1.
       rewrite H0.
       rewrite H1.
       reflexivity.

     - unfold OTSKeyGen_priv.
       fold OTSKeyGen_priv.
       destruct xi0,xi1.
       inversion H0.
       inversion H0.
       inversion H1.

       eapply getSupport_In_Seq.
       instantiate (1:=b).
       simpl.
       apply in_getAllBvectors.

       eapply getSupport_In_Seq.
       instantiate (1:=b0).
       simpl.
       apply in_getAllBvectors.

       inversion H0.
       inversion H1.
       rewrite H3.

       eapply getSupport_In_Seq.
       instantiate (1:=(xi0,xi1)).
       pose proof (IHl n xi0 xi1 H3 H4).
       assumption.

       simpl.
       left.
       reflexivity.
  Qed.


  (* A main lemma *)
  Lemma OTS_keygen_decr : forall l n x0 x1 xi0 xi1 y0 y1 yi0 yi1, 
      In (((x0::xi0)%list, (x1::xi1)%list),((y0::yi0)%list,(y1::yi1)%list)) (getSupport (OTSKeyGen n (S l))) ->
      In ((xi0,xi1),(yi0,yi1)) (getSupport (OTSKeyGen n l)).
  Proof.    
    intros.
    unfold OTSKeyGen in *.
    unfold OTSKeyGen_priv in H0.
    fold OTSKeyGen_priv in H0.
    repeat simp_in_support.
    destruct x. 
    simp_in_support.
    inversion H8.
    inversion H9.
    destruct x4.
    eapply getSupport_In_Seq.
    eauto.
    repeat simp_in_support.
    simpl. left. reflexivity.
  Qed.

  Lemma OTS_keygen_incr : forall l n x0 x1 xi0 xi1 yi0 yi1,
      In (xi0,xi1,(yi0,yi1)) (getSupport (OTSKeyGen n l)) ->
      In ((x0::xi0)%list,(x1::xi1)%list,((H n x0::yi0)%list,(H n x1::yi1)%list))
         (getSupport (OTSKeyGen n (S l))).
  Proof.
    destruct l; intuition.
    - simpl in H0.
      inversion H0.
      inversion H1.
      subst.
      pose proof OTS_keygen_priv_uniform as Priv.
      assert (length (x0::nil) = 1%nat) by reflexivity.
      assert (length (x1::nil) = 1%nat) by reflexivity.
      pose proof (OTS_keygen_priv_uniform 1 n (x0::nil) (x1::nil) H2 H3).
      unfold OTSKeyGen_priv in H4.
      repeat simp_in_support.
      specialize (Priv _ _ _ _ H2 H3) as Keys.
      unfold OTSKeyGen.

      eapply getSupport_In_Seq.
      eassumption.
      simpl.
      left.
      reflexivity.

      exfalso; assumption.

    - unfold OTSKeyGen in H0.
      unfold OTSKeyGen_priv in H0.
      fold OTSKeyGen_priv in H0.
      repeat simp_in_support.
      destruct x.
      destruct x4.
      repeat simp_in_support.

      eapply getSupport_In_Seq.
      (* look at what we need then put everything in the right order *)
      instantiate (1:= ((x0::x2::l2)%list, (x1::x3::l3)%list)).

      unfold OTSKeyGen.
      unfold OTSKeyGen_priv.
      fold OTSKeyGen_priv.
     
      eapply getSupport_In_Seq.
      instantiate (1:=x0).
      unfold getSupport.
      apply in_getAllBvectors.

      eapply getSupport_In_Seq.
      instantiate (1:=x1).
      unfold getSupport.
      apply in_getAllBvectors.

      eapply getSupport_In_Seq.
      instantiate (1:=((x2::l2)%list,(x3::l3)%list)).

      eapply getSupport_In_Seq.
      instantiate (1:=x2).
      unfold getSupport.
      apply in_getAllBvectors.

      eapply getSupport_In_Seq.
      instantiate (1:=x3).
      unfold getSupport.
      apply in_getAllBvectors.

      eapply getSupport_In_Seq.
      eassumption.

      simpl; left; reflexivity.
      simpl; left; reflexivity.
      simpl; left; reflexivity.
  Qed.

  Lemma OTS_keygen_uniform : forall l n l0 l1, 
      length l0 = l -> length l1 = l ->
      In ((l0,l1), (map (H n) l0, map (H n) l1)) (getSupport (OTSKeyGen n l)).
  Proof.
    induction l; intuition;
    specialize (OTS_keygen_priv_uniform _ _ _ _ H0 H1) as Key.
    - simpl.
      unfold OTSKeyGen_priv in Key.
      repeat simp_in_support.
      left.
      simpl.
      reflexivity.

    - unfold OTSKeyGen_priv in Key.
      fold OTSKeyGen_priv in Key.
      repeat simp_in_support.
      destruct x1.
      repeat simp_in_support.
      eapply OTS_keygen_incr.
      eapply IHl.
      inversion H0.
      reflexivity.
      inversion H1.
      reflexivity.
   Qed.

  Lemma OTS_sign_decr : forall n l s ss x0 xi0 x1 xi1 m ms,
      In (s::ss)%list (getSupport (@OTSSign n (S l) ((x0::xi0)%list,(x1::xi1)%list) (m::ms))) ->
      In ss (getSupport (@OTSSign n l (xi0,xi1) ms)).
  Proof.
    intros.
    unfold OTSSign in H0.      
    destruct m;
      fold (@OTSSign n l) in H0;
      repeat simp_in_support;
      inversion H2;
      assumption.
  Qed.

  Lemma OTS_sign_true : forall n l s sig x0 xi0 x1 xi1 msg, 
     In (s::sig)%list (getSupport (@OTSSign n (S l) ((x0::xi0)%list,(x1::xi1)%list) (true::msg))) ->
     s = x1.      
  Proof.
    intros.
    unfold OTSSign in H0.
    repeat simp_in_support.
    inversion H2.
    reflexivity.
  Qed.

  (* APT *)
  Lemma OTS_sign_bit : forall n l s sig x0 xi0 x1 xi1 msg (b : bool),
      In (s::sig)%list (getSupport (@OTSSign n (S l) ((x0::xi0)%list,(x1::xi1)%list) (b::msg))) ->
      s = if b then x1 else x0.
  Proof. 
    intros.
    unfold OTSSign in H0.
    fold @OTSSign in H0.
    fcf_simp_in_support;
    inv H2; auto.
  Qed.
       

  Lemma OTS_verify_length1 : forall n l pubkey msg sig, 
      @OTSVerify n l pubkey msg sig = true ->
      length (fst pubkey) = length sig.
  Proof.
    intros n l [k0 k1] msg sig.
    revert k0 k1 l msg.
    unfold fst.
    induction sig.
     - intuition.
       destruct k0,k1,msg; try reflexivity; try inversion H0.

     - intuition.
       destruct k0,k1,msg; try reflexivity; try inversion H0. 
       apply andb_true_iff in H2 as [H2 H3].
       simpl.
       f_equal.
       eapply IHsig.
       eapply H3.
  Qed.       


  Theorem OTS_correct : forall n l msg sig prikey pubkey,
      In (prikey,pubkey) (getSupport (OTSKeyGen n l)) ->
      In sig (getSupport (@OTSSign n l prikey msg)) ->
      length sig = l -> 
      @OTSVerify n l pubkey msg sig = true. 
  Proof.
    induction l; intros.
    - unfold OTSKeyGen in H0.
      repeat simp_in_support.
      unfold OTSKeyGen_priv in H3.
      repeat simp_in_support.
      pose proof (vector_0 msg).
      subst.
      unfold OTSSign in H1.
      simp_in_support.
      reflexivity.

    - pose proof (vector_S msg).
      inversion H3.
      inversion H4.
      subst.
      destruct pubkey as [k0 k1].
      destruct k0,k1,prikey,l0,l1; try (
      pose proof H0 as Gen;
      apply OTS_keygen_keylengths2 in H0;
      inversion H0;
      inversion H5;
      inversion H6);
      try (specialize (OTS_keygen_keylengths _ _ _ _ _ _ Gen) as Gen1;
      inversion Gen1;
      clear Gen1;
      inversion H7;
      inversion H8;
      inversion H10;
      inversion H11
      ); subst.
      
      specialize (OTS_keygen_decr _ _ _ _ _ _ _ _ _ _ Gen) as Gen1.
      destruct sig.
      inversion H2.
       
      specialize (OTS_sign_decr _ _ _ _ _ _ _ _ _ _ H1) as Sig1.
      pose proof (IHl x0 sig (l0,l1) (k0,k1) Gen1 Sig1).
      apply OTS_keygen_priv_pub in Gen.      
      apply OTS_sign_bit in H1.
      simpl.
      rewrite andb_true_iff.
      inversion Gen.
      subst.
      split.
       + destruct x; try apply eqbBvector_complete.
       + inversion H2.
         apply H8 in H15.
         assumption.
    Qed.


End LamportScheme.



