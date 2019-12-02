Require Import FCF.
Require Import Bvector.
Require Import OWF.
Require Import OTS.
Require Import IndepAnd.


Require Import LamportScheme.


Section Lamport.
  
  Variable n l : nat.
  Hypothesis nz_n : nz n.
  Hypothesis nz_l : nz l. 

  (* Assumed one-way function *)
  Variable H : forall n, Bvector n -> Bvector n.

  (* Purely for readability *)
  Definition Msg (l : nat) := (Bvector l).
  Definition Sig (n : nat) := (list (Bvector n)).
  Definition Keypart (n : nat) := (list (Bvector n)).
  Definition Key (n : nat) := (Keypart n * Keypart n) %type.

  Variable A_state : Set.
  (* A1 asks us for signature *)
  Variable A1 : forall n l, Key n -> Comp (Msg l * A_state).
  Hypothesis wf_A1 : forall n l k, well_formed_comp (A1 n l k).

  (* A2 gives us a forgery *)
  Variable A2 : forall n l, (Sig n * A_state) -> Comp (Msg l * Sig n).
  Hypothesis wf_A2 : forall n l s, well_formed_comp (A2 n l s).

  (* Assume A2 can forge a signature (contrapositive proof) *)
  Axiom A2_successful : forall k m s sig a,
      In (m,s) (getSupport (A2 n l (sig,a))) ->
      OTSVerify H k m s = true.



  (************    Definitions and Theory    ************)

  Open Scope list.

  Fixpoint keyInsertSingle {n : nat} (i : nat) (y : (Bvector n))
                  (keypart : list (Bvector n)) :=
    match keypart with
    | (k::ks) =>
      match i with
      | O => (y::ks)
      | S i' => k :: keyInsertSingle i' y ks
      end
    | nil => nil
    end.

  (* Eventually, we will insert the y that we must invert into the pubkey *)
  Definition keyInsert {n:nat} (i : nat) (r : bool) (y : (Bvector n))
           (key : list (Bvector n) * list (Bvector n)) :=
    match r with
    | false => (keyInsertSingle i y (fst key), snd key)
    | true  => (fst key, keyInsertSingle i y (snd key)) 
    end.


  Lemma keyInsertSingle_spec : forall i j n y keypart, 
      j < length keypart ->
      nth_error (@keyInsertSingle n i y keypart) j =
       if i=?j then Some y else nth_error keypart j.
  Proof.
    induction i; intuition.
    - unfold keyInsertSingle.
      destruct keypart.
      inversion H0.

      simpl.
      destruct j; try reflexivity.

    - unfold keyInsertSingle.
      fold (@keyInsertSingle n).
      destruct keypart.
      inversion H0.

      destruct j; try reflexivity.

      simpl.
      eapply IHi.
      simpl in H0.
      apply lt_S_n in H0; assumption.
   Qed.


  Lemma keyInsertSingle_map : forall i n f x k,
     @keyInsertSingle n i (f x) (map f k) = map f (@keyInsertSingle n i x k).
  Proof.
    induction i; intuition.
    - simpl.
      destruct k.
      destruct (map f nil) eqn:map.
      reflexivity.
      inversion map.
      destruct (map f (b :: k)) eqn:map.
      inversion map.
      inversion map.
      simpl.
      reflexivity.

    - unfold keyInsertSingle.
      fold (@keyInsertSingle n0 i).
      destruct k.
      destruct (map f nil) eqn:map.
      reflexivity.
      inversion map.

      destruct (map f (b ::k)) eqn:map;
      inversion map.
      subst.
      simpl.
      f_equal.
      apply IHi.
   Qed.

  (* To lookup the value of an element of a bitvector *)
  Definition ith_element {n : nat} (v : (Bvector n)) (i : nat) :=
    nth_error (Vector.to_list v) i.

  Lemma ith_element_safe : forall i (m : Bvector l) b, 
    l > 0 -> i < l -> ith_element m i = b -> b <> None.
  Proof.
    clear.
    intuition.
    unfold ith_element in H1.
    destruct (length (Vector.to_list m)) eqn :?.
    rewrite to_list_length in Heqn.
    omega.

    destruct (Vector.to_list m) eqn :?.
    inversion Heqn.

    destruct (nth_error (b0::l0) i) eqn :?. 
    congruence.

    rewrite nth_error_None in Heqo.
    rewrite Heqn in Heqo.
    assert (length (Vector.to_list m) = length (b0::l0)).
    f_equal; assumption.

    rewrite to_list_length in H3.
    rewrite Heqn in H3.
    rewrite <- H3 in Heqo.
    omega.
  Qed.
        

  (* useful lemma to simplify proofs *)
  Lemma to_list_decr : forall n (m : Vector.t bool n) (h : bool) x xs,
      Vector.to_list (h::m)%vector = (x::xs)%list ->
      Vector.to_list m = xs.
  Proof.
    destruct m; intuition.
    - unfold Vector.to_list in *.
      inversion H0.
      reflexivity.

    - destruct xs. 
      specialize (to_list_length (h0::h::m)%vector) as L.
      assert (length (Vector.to_list (h0::h::m)%vector) = length (x::nil)).
      f_equal.
      assumption.
      rewrite L in H1.
      simpl in H1.
      omega.

      inversion H0.
      rewrite H4.
      unfold Vector.to_list.
      f_equal.
      rewrite H4.
      reflexivity.
   Qed.

  (* The ith-element of a Bvector (with valid index) is true or false *)
  Lemma ith_element_either : forall i l (m : Bvector l) b,
      l > 0 -> i < l -> 
      (ith_element m i ?= Some b) = true \/
      (ith_element m i ?= Some (negb b)) = true.
  Proof.
    induction i; intuition.
    - destruct m; [inversion H0 | ].
      destruct h, b;
      unfold ith_element, nth_error, Vector.to_list.
      left; apply eqb_refl. 
      right; unfold negb; apply eqb_refl.
      right; unfold negb; apply eqb_refl. 
      left; apply eqb_refl.

    - destruct m; [inversion H0 | ].
      destruct n0.
      inversion H1.
      inversion H3.

      unfold ith_element.
      destruct (length (Vector.to_list (h::m)%vector)) eqn:L.
      rewrite to_list_length in L.
      inversion L.
      destruct (Vector.to_list _) eqn:M.
      inversion L.
      simpl.
      unfold ith_element in IHi.    
      apply to_list_decr in M.

      rewrite <- M.
      eapply IHi.
      omega.
      omega.
  Qed.

  (* returns all the key elements in the "path" of m *)
  (* "path": the l-elements corresponding to each column of a key
   where false touches the top row and true touches the bottom.
   e.g. OTSSign returns the "path" of the message through the privkey *)
  Fixpoint keyValues (n l : nat) (k : list (Bvector n) * list (Bvector n))
                      (m : (Bvector l)) : list (Bvector n) :=
    match k with
    | (nil,nil) => nil
    | (y0::y0s%list, y1::y1s%list) =>
      match m with
      | Vector.nil _ => nil
      | Vector.cons _ b l' ms => (if b then y1 else y0)
                                  :: keyValues n l' (y0s,y1s) ms
      end
    | _ => nil
    end.

  (* The symmetric lemma is also true but we need only one *)
  Lemma keyInsert_length : forall k0 k1 i r y, 
      length (fst (@keyInsert n i r y (k0,k1))) = length k0.
  Proof.
    induction k0; intuition.
    - destruct k1;
      destruct i,r;
      (destruct n; [inversion nz_n; omega | ]);
      simpl; try reflexivity.
    - destruct k1 eqn:K;
      destruct i,r;
      (destruct n; [inversion nz_n; omega | ]);
      try (simpl; reflexivity).
      simpl.
      specialize (IHk0 nil i false y) as IH.
      unfold keyInsert in IH.
      unfold fst,snd in IH.
      f_equal.
      apply IH.
      
      specialize (IHk0 (b::l0)%list i false y) as IH.
      unfold keyInsert in IH.
      unfold fst,snd in IH.
      simpl.
      f_equal.
      apply IH.
  Qed.

  (* Since OTSKeyGen_priv is uniform, we can insert any bitvector
   as long as we maintain the replationship between the keys *)
  Lemma OTS_keygen_uniform_keyInsert : forall l4 x r x1 l5 l,
      In (l4,l5) (getSupport (OTSKeyGen_priv n l)) ->
      In (keyInsert x r x1 (l4, l5),
          keyInsert x r (H n x1) (map (H n) l4, map (H n) l5))
         (getSupport (OTSKeyGen H n l)).        
  Proof.
    induction l4, l5; intuition.
    - apply OTS_keygenpriv_keylengths in H0.
      inversion H0.
      simpl in H1.
      subst.
      simpl.
      left.
      destruct x,n,r;
      unfold keyInsert,fst,snd,keyInsertSingle; reflexivity.

    - apply OTS_keygenpriv_keylengths in H0.
      inversion H0.
      simpl in H1.
      simpl in H2.
      omega.
     
    - apply OTS_keygenpriv_keylengths in H0.
      inversion H0.
      simpl in H1.
      simpl in H2.
      omega.

    - destruct l0.
      simpl in H0.
      inversion H0.
      inversion H1.
      exfalso; assumption.

      destruct x.
      destruct r.
      destruct n; [inversion nz_n; omega| ].
      unfold keyInsert, fst, snd.
      unfold keyInsertSingle.
      destruct (map (H (S n0)) (b::l5)) eqn:M;
      inversion M.
      assert ((H (S n0) a::map (H (S n0)) l4)%list = (map (H (S n0)) (a::l4))).
      simpl;reflexivity.
      rewrite <- H1.
      eapply OTS_keygen_incr.
      eapply OTS_keygen_uniform;
      apply OTS_keygenpriv_keylengths in H0;
      inversion H0 as [L4 L5];
      simpl in L4;
      simpl in L5;
      omega.

      destruct n; [inversion nz_n; omega| ].
      unfold keyInsert, fst, snd.
      unfold keyInsertSingle.
      destruct (map (H (S n0)) (b::l5)) eqn:M;
      inversion M.
      assert ((H (S n0) a::map (H (S n0)) l4)%list = (map (H (S n0)) (a::l4))).
      simpl;reflexivity.
      rewrite <- H1.
      eapply OTS_keygen_incr.
      eapply OTS_keygen_uniform;
      apply OTS_keygenpriv_keylengths in H0;
      inversion H0 as [L4 L5];
      simpl in L4;
      simpl in L5;
      omega.

      destruct n; [inversion nz_n; omega |].
      destruct r.

      unfold keyInsert.
      unfold fst, snd.
      specialize (IHl4 (x) true x1 (l5)%list l0) as IH.
      unfold keyInsert in IH.
      unfold fst,snd in IH.
      unfold keyInsertSingle.
      fold (@keyInsertSingle (S n0)).

      destruct (map (H (S n0)) (b :: l5)) eqn:M;
      inversion M.

      assert ((H (S n0) a :: map (H (S n0)) l4)%list = (map (H (S n0)) (a::l4))).
      simpl; reflexivity.
      rewrite <- H1.
      eapply OTS_keygen_incr.
      eapply IH.
      eapply OTS_keygen_priv_uniform;
      apply OTS_keygenpriv_keylengths in H0;
      inversion H0 as [L4 L5];
      simpl in L4;
      simpl in L5;
      omega.

      unfold keyInsert.
      unfold fst, snd.
      specialize (IHl4 (x) false x1 (l5)%list l0) as IH.
      unfold keyInsert in IH.
      unfold fst,snd in IH.
      unfold keyInsertSingle.
      fold (@keyInsertSingle (S n0)).

      destruct (map (H (S n0)) (b :: l5)) eqn:M;
      inversion M.

      assert ((H (S n0) a :: map (H (S n0)) l4)%list = (map (H (S n0)) (a::l4))).
      simpl; reflexivity.
      rewrite <- H1.
      eapply OTS_keygen_incr.
      eapply IH.
      eapply OTS_keygen_priv_uniform;
      apply OTS_keygenpriv_keylengths in H0;
      inversion H0 as [L4 L5];
      simpl in L4;
      simpl in L5;
      omega.
  Qed.
      
      
  (* Basic behavior of OTSVerify *)
  (* This result is central to the reduction since it links forging 
   with inverting (through the relationship between the keys) *)
  Lemma OTSVerify_spec : forall i l prikey pubkey (m : Bvector l) s x' x,
      l > 0 -> 
      In (prikey, pubkey) (getSupport (OTSKeyGen H n l)) ->           
      OTSVerify H pubkey m s = true ->
      nth_error s i = Some x' -> 
      nth_error (keyValues n l pubkey m) i = Some (H n x) -> 
      eqbBvector (H n x') (H n x) = true.
  Proof.
    (* Reasoning : 
         You have (m,s) as a valid pair under a legit pubkey
             (i.e. "map" H onto s = keyValues n l pubkey m ) 
         the ith-element of s is x', and 
         the ith-element of m's path through the pubkey is (H n x)
             (i.e. H n x' = H n x )
     *)
    (* Note: this almost certainly "should" have been by induction on l0 *)
    induction i; intuition.
    -  unfold nth_error in H3.
       destruct s.
       specialize (OTS_verify_length1 H _ _ _ _ _ H2). 
       intuition.
       specialize (OTS_keygen_keylengths2 _ _ _ _ _ _ _ H1) as Key.
       apply OTS_keygen_keylengths in H1.
       inversion Key.
       inversion H1.
       unfold fst in H5.
       rewrite H6 in H8.
       rewrite <- H8 in H5.
       simpl in H5.
       omega.

       specialize (OTS_keygen_keylengths2 _ _ _ _ _ _ _ H1) as Keys.
       destruct a,b,a0,b0; try (
       simpl in *;
       omega);
       (specialize (OTS_keygen_keylengths _ _ _ _ _ _ _ H1) as Keys';
       inversion Keys';
       inversion H5;
       inversion H6;
       clear Keys; clear Keys';
       clear H5; clear H6; clear H8; clear H9).

       specialize (OTS_keygen_priv_pub_r _ _ _ _ _ _ _ H1) as Keys.
       apply OTS_keygen_priv_pub_l in H1.
       destruct m. inversion H0.
       simpl in H2.
       apply andb_true_iff in H2.
       inversion H2.
       simpl in H4.
       destruct h.
       apply eqbBvector_sound in H5.
       inversion H3. inversion H4.
       subst.
       rewrite H9.
       eapply eqbBvector_complete.
       eapply eqbBvector_sound in H5.
       inversion H3. inversion H4.
       subst.
       rewrite H9.
       apply eqbBvector_complete. 

    - destruct s; try inversion H3.
      destruct a0.
      apply OTS_verify_length1 in H2.
      inversion H2.
      destruct b0.
      specialize (OTS_keygen_keylengths _ _ _ _ _ _ _ H1) as Keys.
      apply OTS_keygen_keylengths2 in H1.
      inversion H1.
      inversion Keys.
      rewrite H7 in H9.
      simpl in H9.
      omega.

      destruct m. 
      inversion H0.

      destruct a,b;
      specialize (OTS_keygen_keylengths _ _ _ _ _ _ _ H1) as Keys;
      inversion Keys;
      simpl in H5;
      simpl in H7;
      try omega.


      apply OTS_keygen_decr in H1.

      clear Keys; clear H5; clear H7.
      destruct n0.
        + simpl in H4.
          simpl in H2.
          rewrite andb_true_iff in H2.
          inversion H2.
          destruct s,i.
          
          unfold nth_error in H6.
          inversion H6.
          simpl in H6.
          inversion H6.


          specialize (OTS_keygen_keylengths2 _ _ _ _ _ _ _ H1) as Keys.
          inversion Keys.
          apply OTS_keygen_keylengths in H1.
          inversion H1.
          rewrite length_zero_iff_nil in H8.
          rewrite length_zero_iff_nil in H9.
          rewrite H8 in H10.
          rewrite H9 in H11.
          simpl in H10.
          simpl in H11.
          symmetry in H10.
          rewrite length_zero_iff_nil in H10.
          symmetry in H11.
          rewrite length_zero_iff_nil in H11.
          subst.
          apply OTS_verify_length1 in H7.
          unfold fst in H7.
          inversion H7.


          specialize (OTS_keygen_keylengths2 _ _ _ _ _ _ _ H1) as Keys.
          inversion Keys.
          apply OTS_keygen_keylengths in H1.
          inversion H1.
          rewrite length_zero_iff_nil in H8.
          rewrite length_zero_iff_nil in H9.
          rewrite H8 in H10.
          rewrite H9 in H11.
          simpl in H10.
          simpl in H11.
          symmetry in H10.
          rewrite length_zero_iff_nil in H10.
          symmetry in H11.
          rewrite length_zero_iff_nil in H11.
          subst.
          apply OTS_verify_length1 in H7.
          unfold fst in H7.
          inversion H7.


        + eapply IHi.
          instantiate (1:=S n0).
          omega.
   
          eassumption.
   
          simpl in H2.
          rewrite andb_true_iff in H2.
          inversion H2.
          eassumption.
          
          assumption.
   
          simpl in H4.
          assumption.
  Qed.


  (* Basic behavior of keyInsert. 
     If you insert a value at i, then nth_error i will recover it *)
  Lemma keyValues_keyInsert : forall i r y pubkey prikey l (msg:Bvector l),
      i < l -> 
      In (prikey,pubkey) (getSupport (OTSKeyGen H n l)) -> 
      (ith_element msg i ?= Some r) = true -> 
      nth_error (keyValues n l (keyInsert i r y pubkey) msg) i = Some y.
  Proof.
    intros i r; revert i.
    induction i; intuition.
    - simpl.
      destruct a,b;
      specialize (OTS_keygen_keylengths _ _ _ _ _ _ _ H1) as Keys;
      apply OTS_keygen_keylengths2 in H1;
      inversion H1;
      inversion Keys;
      try rewrite H3 in H5;
      try rewrite H3 in H6;
      simpl in H5;
      simpl in H6;
      try omega.
      
      destruct r.
      destruct n eqn:N; inversion nz_n; try omega;
      unfold keyInsert.
      unfold fst,snd.
      simpl.

      destruct msg; try omega.
      simpl.
      unfold ith_element in H2.
      simpl in H2.
      destruct h eqn:Row.
      reflexivity.
      rewrite eqb_leibniz in H2.
      inversion H2.

      destruct n; inversion nz_n; try omega.

      destruct msg; try omega.
      simpl.
      destruct h.
      unfold ith_element in H2.
      simpl in H2.
      rewrite eqb_leibniz in H2.
      inversion H2.
      reflexivity.

    - simpl.
      destruct a,b;
      try (specialize (OTS_keygen_keylengths _ _ _ _ _ _ _ H1) as Keys;
      apply OTS_keygen_keylengths2 in H1;
      inversion H1;
      inversion Keys;
      try rewrite H3 in H5;
      try rewrite H3 in H6;
      simpl in H5;
      simpl in H6;
      omega).
     
      destruct n; inversion nz_n; try omega.
      destruct msg; try omega.
      destruct a0,b0;
      try specialize (OTS_keygen_keylengths2 _ _ _ _ _ _ _ H1) as Keys;
      inversion Keys;
      simpl in H3;
      simpl in H4;
      try omega.

      (* Everything we need for IHi *)
      apply OTS_keygen_decr in H1.
      assert (i < n1) by omega.
      assert (ith_element (h::msg)%vector (S i)
              = ith_element msg i) by intuition.

      unfold keyInsert in IHi.
      pose proof (IHi y (a,b2) (a0,b4) n1 msg) as IH.
      unfold fst,snd in IH.

      destruct r.
      simpl.
      apply IH; try assumption.

      simpl.
      apply IH; try assumption.
  Qed.


  (* The signature is unaffected by insertion if the inserted
   element is not in the path of the message *)
   Lemma OTS_sign_untouched : forall i r l x k (m : Bvector l),
       In k (getSupport (OTSKeyGen_priv n l)) -> 
       negb (ith_element m i ?= Some r) = true -> 
       @OTSSign n l (keyInsert i r x k) m = @OTSSign n l k m. 
   Proof.
     intros i r; revert i.
     induction i; intuition.
     - destruct a,b;
       apply OTS_keygenpriv_keylengths in H0;
       inversion H0 as [F S];
       simpl in F;
       simpl in S.

       destruct m.
       reflexivity. 
       destruct n; [inversion nz_n; omega | ].
       destruct r; reflexivity.
       omega.
       omega.
       
       destruct m; [omega | ].
       destruct n; [inversion nz_n; omega | ].
       destruct r.
       simpl.
       destruct h.
       unfold ith_element, nth_error, Vector.to_list in H1.
       rewrite eqb_refl in H1.
       unfold negb in H1.
       inversion H1.

       reflexivity.

       simpl.
       destruct h.
       reflexivity.
       unfold ith_element, nth_error, Vector.to_list in H1.
       rewrite eqb_refl in H1.
       unfold negb in H1.
       inversion H1.

     - destruct a,b;
       specialize(OTS_keygenpriv_keylengths _ _ _ _ H0) as Key;
       inversion Key as [F S];
       simpl in F;
       simpl in S.

       destruct m.
       reflexivity.
       omega.
       omega.
       omega.
       
       destruct n; [inversion nz_n; omega | ].
       destruct r.
       + unfold keyInsert, fst, snd.
         unfold keyInsertSingle.
         fold (@keyInsertSingle (Datatypes.S n0)).
         destruct m.
         simpl; reflexivity.
         destruct h.

         * simpl.
           f_equal.
           specialize (IHi n1 x (a,b1) m) as IH.
           unfold keyInsert in IH.
           unfold fst,snd in IH.
           eapply IH.
           eapply OTS_keygen_priv_uniform;
           apply OTS_keygenpriv_keylengths in H0;
           inversion H0 as [A B];
           simpl in A;
           simpl in B;
           omega.
           unfold ith_element in H1.
           assert (nth_error (true::Vector.to_list m) (Datatypes.S i)
                   = nth_error (Vector.to_list m) i).
           simpl; reflexivity.
           destruct (Vector.to_list (true::m)%vector) eqn:V.
           inversion V.
           simpl in H1.
           apply to_list_decr in V.
           unfold ith_element.
           rewrite V.
           assumption.

         * simpl.
           f_equal.
           specialize (IHi n1 x (a,b1) m) as IH.
           unfold keyInsert in IH.
           unfold fst,snd in IH.
           eapply IH.
           eapply OTS_keygen_priv_uniform;
           apply OTS_keygenpriv_keylengths in H0;
           inversion H0 as [A B];
           simpl in A;
           simpl in B;
           omega.
           unfold ith_element in H1.
           assert (nth_error (true::Vector.to_list m) (Datatypes.S i)
                   = nth_error (Vector.to_list m) i).
           simpl; reflexivity.
           destruct (Vector.to_list (false::m)%vector) eqn:V.
           inversion V.
           simpl in H1.
           apply to_list_decr in V.
           unfold ith_element.
           rewrite V.
           assumption.
       
       + unfold keyInsert, fst, snd.
         unfold keyInsertSingle.
         fold (@keyInsertSingle (Datatypes.S n0)).
         destruct m.
         simpl; reflexivity.
         destruct h.

         * simpl.
           f_equal.
           specialize (IHi n1 x (a,b1) m) as IH.
           unfold keyInsert in IH.
           unfold fst,snd in IH.
           eapply IH.
           eapply OTS_keygen_priv_uniform;
           apply OTS_keygenpriv_keylengths in H0;
           inversion H0 as [A B];
           simpl in A;
           simpl in B;
           omega.
           unfold ith_element in H1.
           assert (nth_error (true::Vector.to_list m) (Datatypes.S i)
                   = nth_error (Vector.to_list m) i).
           simpl; reflexivity.
           destruct (Vector.to_list (true::m)%vector) eqn:V.
           inversion V.
           simpl in H1.
           apply to_list_decr in V.
           unfold ith_element.
           rewrite V.
           assumption.

         * simpl.
           f_equal.
           specialize (IHi n1 x (a,b1) m) as IH.
           unfold keyInsert in IH.
           unfold fst,snd in IH.
           eapply IH.
           eapply OTS_keygen_priv_uniform;
           apply OTS_keygenpriv_keylengths in H0;
           inversion H0 as [A B];
           simpl in A;
           simpl in B;
           omega.
           unfold ith_element in H1.
           assert (nth_error (true::Vector.to_list m) (Datatypes.S i)
                   = nth_error (Vector.to_list m) i).
           simpl; reflexivity.
           destruct (Vector.to_list (false::m)%vector) eqn:V.
           inversion V.
           simpl in H1.
           apply to_list_decr in V.
           unfold ith_element.
           rewrite V.
           assumption.
   Qed.





  (**********************    Sequence of Games    **********************)

    (* Final Goal : 
     (1/2) * (1/l) * OTSigForge_Advantage <= Invert_Advantage 

    Idea: we are given y and need to return x such that H x = y to win the 
    Invert game. For A2 to win at the Forge game, it must return a path 
    through the public key (message) and corresponding path through the 
    private key (signature). Since pubkey = "map" H prikey, the signature 
    is a list of inverses under H. Therefore, if we insert y into the public
    key AND A2 returns a message whose path touches y, the signature will 
    contain the inverse we require. 

    There is a 1/2 chance the message's path touches the insertion row and 
    at least a 1/l chance the adversary's message differs from the queried 
    message in the right column (the messages could differ in more than one 
    place). Thus, we have at least a 1/2l chance that the adversary's 
    (successful) forgery inverts y for us. 
    
    Since (1/2)*(1/l) is polynomial, any adversary which can successfully
    forge a signature in polynomial time, can also invert H in polynomial
    time. We assume that H is a one-way function so we can conclude that 
    no adversary can successfully forge a signature in the Lamport scheme. 
    *)


  (* simplification of the Forge game *)
  Definition A_forges := 
    k <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a2 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a2;
    if msg' ?= msg then ret false
    else ret OTSVerify H pubkey msg' sig'.

  Lemma OTSigForge_A_forges : 
    OTSigForge_Advantage _ _ _ _ _ (OTSKeyGen H n l) OTSSign (OTSVerify H) _ (A1 n l) (A2 n l) == Pr[A_forges].
  Proof.
    reflexivity.
  Qed.

   (******************    0. Format initial game    **********************)  

  (* we sample a random insertion point but do nothing with it *)
  Definition A_forges_inv := 
    i <-$ [0..l);
    r <-$ {0,1};
    k <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a2 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a2;
    if negb (msg' ?= msg)
    then ret OTSVerify H pubkey msg' sig'
    else ret false.

    
  Lemma A_forges_A_forges_inv :
    Pr[A_forges] == Pr[A_forges_inv].
  Proof.
    unfold A_forges, A_forges_inv.
    fcf_irr_r; [apply well_formed_RndNat | ].
    inversion nz_l; assumption.
    fcf_irr_r.
    apply well_formed_Bind.
    apply well_formed_Rnd.
    intuition.
    apply well_formed_Ret.
    fcf_skip.
    fcf_simp.
    fcf_skip.
    fcf_simp.
    fcf_skip.
    fcf_skip.
    fcf_simp.
    fcf_compute.
  Qed.


  (******************    1. Pick up 1/l term    **********************)  

  (* we now check that the message we signed and the message 
   A2 is attempting to forge with differ at the insertion column *)
  Definition Game1 := 
    i <-$ [0..l);
    r <-$ {0,1};
    k <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a1 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a1;
    (* Pr[column] = 1/l *)
    column <- negb (ith_element msg i ?= ith_element msg' i);
    if negb (msg' ?= msg) && column
    then ret OTSVerify H pubkey msg' sig'
    else ret false.
 

  (* Tells us the first place where the lists differ *)
  (* Importantly, assumes the lists are different *)
  Fixpoint firstDiffer (xs ys : list bool) := 
    match xs,ys with
    | (x::xs),(y::ys) =>
      if x?=y then S (firstDiffer xs ys) else O                        
    | _,_ => O
    end.               

  (* Any firstDiffer function must have the following 2 properties: *)

  (* 1: the lists are different where firstDiffer claims *)
  Lemma firstDiffer_different : forall (m m' : Bvector l) i,
      (Vector.to_list m) <> Vector.to_list m' -> 
      (firstDiffer (Vector.to_list m) (Vector.to_list m') ?= i) = true -> 
      (@ith_element l m i ?= @ith_element l m' i) = false.
  Proof.
    induction m eqn:M; intuition.
    - inversion nz_l; omega.
    - assert (length (Vector.to_list (h::b)%vector)=length (Vector.to_list m')).
      rewrite to_list_length.
      rewrite to_list_length.
      reflexivity.

      destruct m' eqn:M'. 
      inversion nz_l; omega.
      rewrite to_list_length in H2.
      rewrite to_list_length in H2.
      inversion H2.
      subst n1.

      destruct (Vector.to_list (h::b)%vector) eqn:vM, 
               (Vector.to_list (h0::b0)%vector) eqn:vM'.
      inversion vM.
      inversion vM.
      inversion vM'.

      destruct n0.
      pose proof (vector_0 b).
      pose proof (vector_0 b0).
      subst.
      inversion vM.
      inversion vM'.
      subst.
      simpl in H0.
      destruct i.
      destruct (b1?=b2) eqn:?.
      rewrite eqb_leibniz in H1.
      inversion H1.
      rewrite Heqb in H4.
      inversion H4.
      unfold ith_element.
      simpl.
      rewrite eqb_false_iff in *.
      intuition.
      inversion H3.
      intuition.
      
      destruct (b1?=b2) eqn:?.
      rewrite eqb_leibniz in Heqb.
      subst b2.
      intuition.

      simpl in H1.
      rewrite Heqb in H1.
      rewrite eqb_leibniz in H1.
      inversion H1.

      destruct i.
      + unfold ith_element.
        rewrite vM.
        rewrite vM'.
        simpl in H1.
        simpl.
        destruct (Some b1?=Some b2) eqn:B.
        rewrite eqb_leibniz in B.
        inversion B.
        rewrite <- eqb_leibniz in H4.
        rewrite H4 in H1.
        rewrite eqb_leibniz in H1.
        inversion H1.
        reflexivity.      

      + unfold ith_element.
        rewrite vM.
        rewrite vM'.
        simpl.
        unfold ith_element in IHb.
        apply to_list_decr in vM.
        apply to_list_decr in vM'.
        rewrite <- vM.
        rewrite <- vM'.

        eapply IHb.
        intuition.

        eauto.

        rewrite vM.
        rewrite vM'.
        destruct (b1?=b2) eqn:?.
        rewrite eqb_leibniz in Heqb3.
        subst b2.
        intuition.
        rewrite H3 in H0.
        intuition.
        simpl in H1.
        rewrite Heqb3 in H1.
        rewrite eqb_leibniz in H1.
        inversion H1.

        subst.
        inversion H1.
        destruct (b1?=b2).
        destruct (firstDiffer _ _ ?= i) eqn:?.
        symmetry.
        rewrite eqb_leibniz.
        f_equal.
        rewrite eqb_leibniz in Heqb3.
        assumption.

        symmetry.
        rewrite eqb_false_iff.
        rewrite eqb_false_iff in Heqb3.
        intuition.

        rewrite eqb_leibniz in H4.
        inversion H4. 
  Qed.

  (* 2: firstDiffer does not go "out of bounds" *)
  Lemma firstDiffer_bounds : forall m m' d,
      Vector.to_list m <> Vector.to_list m' -> 
      firstDiffer (@Vector.to_list bool l m) (@Vector.to_list bool l m') = d ->
      (d < l)%nat.
  Proof.
    induction m eqn:M; intuition.
    - inversion nz_l; omega.
    - assert (length (Vector.to_list (h::t)%vector)=length (Vector.to_list m')).
      rewrite to_list_length.
      rewrite to_list_length.
      reflexivity.

      destruct m' eqn:M'.
      inversion nz_l; omega.
      rewrite to_list_length in H2.
      rewrite to_list_length in H2.
      inversion H2.
      subst n1.
      clear H2.

      destruct (Vector.to_list (h::t)%vector) eqn:vM,
               (Vector.to_list (h0::t0)%vector) eqn:vM'; 
      try (simpl in H1;
      omega). 
      
      simpl in H1.
      destruct (b?=b0) eqn:B; try omega.
      rewrite eqb_leibniz in B.
      apply to_list_decr in vM.
      apply to_list_decr in vM'.
      rewrite <- H1.
      apply lt_n_S.

      eapply IHt.

      destruct n0.
      pose proof (vector_0 t).
      pose proof (vector_0 t0).
      subst.

      intuition.
      intuition.

      eauto.

      rewrite vM.
      rewrite vM'.
      subst b0. 
      intuition.
      rewrite H2 in H0.
      intuition.

      subst.
      reflexivity.
  Qed.

  (* checks that i is the first position at which the messages differ *)
  Definition Game1_first := 
    i <-$ [0..l); 
    r <-$ {0,1};
    k <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a1 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a1;
    (* this check is sufficient for the "column" check by property 1 *)
    firstColumn <-(firstDiffer (Vector.to_list msg) (Vector.to_list msg') ?= i);
    if negb (msg' ?= msg) && firstColumn 
    then ret OTSVerify H pubkey msg' sig'
    else ret false.

  Lemma Game1_first_Game1 :
    Pr[Game1_first] <= Pr[Game1].
  Proof.
    unfold Game1_first, Game1.
    fcf_skip.
    fcf_skip.
    fcf_skip.
    fcf_simp.
    fcf_skip.
    fcf_simp.
    fcf_skip.
    fcf_skip.
    fcf_simp.
    destruct (m0?=m) eqn:D; try reflexivity.
    destruct (firstDiffer _ _ ?= _) eqn:F.
    apply firstDiffer_different in F.
    rewrite F.
    simpl; reflexivity.
    rewrite eqb_false_iff in D.
    intuition.
    apply to_list_eq_inv in H6.
    intuition.

    rewrite andb_false_r.
    fcf_compute.
    reflexivity.
  Qed.

  (* replaces the previous two checks with an independent but 
   probabilistically equivalent check of i against a fixed value (0) *)
  Definition Game1_i :=
    i <-$ [0..l); 
    r <-$ {0,1};
    k <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a1 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a1;
    if negb (msg' ?= msg) && (i?=0%nat)
    then ret OTSVerify H pubkey msg' sig'
    else ret false.

  (* These checks have the same probability *)
  Lemma Game1_i_Game1_first :
    Pr[Game1_i] == Pr[Game1_first].
  Proof.
    unfold Game1_i, Game1_first.
    fcf_swap fcf_left.
    fcf_swap fcf_right.
    fcf_skip.
    fcf_swap fcf_left.
    fcf_swap fcf_right.
    fcf_skip.
    fcf_simp.
    fcf_swap fcf_left.
    fcf_swap fcf_right.
    fcf_skip.
    fcf_simp.
    fcf_swap fcf_left.
    fcf_swap fcf_right.
    fcf_skip.
    fcf_swap fcf_left.
    fcf_swap fcf_right.
    fcf_skip.
    fcf_simp.
    destruct (m0?=m) eqn:D; try reflexivity.
    
   
    (* use distro_iso_eq here *) 
    remember (firstDiffer (Vector.to_list m) (Vector.to_list m0)) as d.
    destruct (d ?= 0%nat) eqn:?.
    rewrite eqb_leibniz in Heqb.
    rewrite Heqb.
    fcf_skip.
    rewrite eqb_symm.
    reflexivity.

    (* we need a bijection f such that when d = a0, (f a0) = 0 and 
                                       when d=/=a0, (f a0) =/= 0 *)
    eapply (distro_iso_eq
              (fun a0 => if (d=?a0) then 0 else (if (a0=?0) then d else a0))
              (fun a0 => if (d=?a0) then 0 else (if (a0=?0) then d else a0)))%nat.
    clear.
    intuition.
    destruct (d=?x) eqn:D.
    destruct (d=?0) eqn:Z.
    apply Nat.eqb_eq in D.
    apply Nat.eqb_eq in Z.
    subst. reflexivity.

    rewrite Nat.eqb_refl.
    apply Nat.eqb_eq in D.
    assumption.

    destruct (x=?0) eqn:Z.
    rewrite Nat.eqb_refl.
    apply Nat.eqb_eq in Z.
    symmetry. assumption.

    rewrite D.
    rewrite Z.
    reflexivity.


    clear.
    intuition.
    destruct (d=?x) eqn:D.
    destruct (d=?0) eqn:Z.
    apply Nat.eqb_eq in D.
    apply Nat.eqb_eq in Z.
    subst. reflexivity.

    rewrite Nat.eqb_refl.
    apply Nat.eqb_eq in D.
    assumption.

    destruct (x=?0) eqn:Z.
    rewrite Nat.eqb_refl.
    apply Nat.eqb_eq in Z.
    symmetry. assumption.

    rewrite D.
    rewrite Z.
    reflexivity.

    intuition.
    apply in_getSupport_RndNat.
    destruct (d=?x1).
    apply nz_l; omega.
    destruct (x1=?0).
    symmetry in Heqd.
    apply firstDiffer_bounds in Heqd.
    assumption.
    rewrite eqb_false_iff in D.
    intuition.
    apply to_list_eq_inv in H6.
    intuition.
    
    apply RndNat_support_lt in H5.
    assumption.

    intuition.
    apply RndNat_uniform.
    destruct (d=?x1).
    apply nz_l; omega.
    destruct (x1=?0).
    symmetry in Heqd.
    apply firstDiffer_bounds in Heqd.
    assumption.
    rewrite eqb_false_iff in D.
    intuition.
    apply to_list_eq_inv in H6.
    intuition.
    all: try (apply RndNat_support_lt in H5; assumption).

    intuition.
    destruct (d=?x1) eqn:?.
    rewrite Nat.eqb_eq in Heqb0.
    subst x1.
    rewrite eqb_refl.
    rewrite eqb_refl.
    reflexivity.

    destruct (x1=?0) eqn:?.
    rewrite Nat.eqb_neq in Heqb0.
    rewrite <- eqb_false_iff in Heqb0.
    rewrite Heqb0.
    rewrite Heqb.
    reflexivity.

    rewrite Nat.eqb_neq in Heqb0.
    rewrite <- eqb_false_iff in Heqb0.
    rewrite Heqb0.
    rewrite Nat.eqb_neq in Heqb1.
    rewrite <- eqb_false_iff in Heqb1.
    rewrite Heqb1.
    reflexivity.
  Qed.


  (* Rewriting in the form of indep_and *)
  (* Importantly, i is not used in the lower-half *)
  Definition Game1_indep :=
    a <-$ (i <-$ [0..l); ret i?=0%nat);
    r <-$ ( _ <-$ {0,1};
    k <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a1 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a1;
    if negb (msg' ?= msg) 
    then ret OTSVerify H pubkey msg' sig'
    else ret false);
    ret (a && r).

  Lemma Game1_indep_Game1_i : 
    Pr[Game1_indep] == Pr[Game1_i].
  Proof.
    unfold Game1_indep, Game1_i.
    fcf_inline_first.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    fcf_inline fcf_left.
    fcf_simp.
    fcf_skip.
    fcf_simp.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_inline_first.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    destruct (negb (m0 ?= m)) eqn:D;
    fcf_compute.
    rewrite andb_false_r in e0.
    inversion e0.
  Qed.    


  Lemma A_forges_Game1_indep :
    (1/l) * Pr[A_forges_inv] == Pr[Game1_indep].
  Proof.
    unfold A_forges_inv, Game1_indep.
    rewrite indep_and.
    apply ratMult_eqRat_compat.

    assert (Pr[i<-$[0..l); ret i?=0%nat]
            == Pr[i<-$[0..l); ret 0%nat?=i]).
    fcf_skip.
    rewrite eqb_symm.
    reflexivity.

    rewrite H0.
    rewrite <- evalDist_event_equiv.
    rewrite RndNat_prob.
    reflexivity.
    apply nz_l.
    
    fcf_irr_l; try apply well_formed_RndNat.
    apply nz_l.
  Qed.
    
    
  Theorem step1 :
    (1/l) * Pr[A_forges] <= Pr[Game1].
  Proof.
    eapply leRat_trans.
    apply eqRat_impl_leRat.
    rewrite A_forges_A_forges_inv.
    apply A_forges_Game1_indep.
    rewrite Game1_indep_Game1_i.
    rewrite Game1_i_Game1_first.
    rewrite Game1_first_Game1.
    reflexivity.
  Qed.

    (******************    2. Pick up 1/2 term    **********************)    

  Definition Game2 :=
    i <-$ [0..l);
    r <-$ {0,1};
    k <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a2 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a2;
    column <- negb (ith_element msg i ?= ith_element msg' i);
    (* Pr[row] = 1/2 *)
    row <- negb (ith_element msg i ?= Some r);
    if negb (msg' ?= msg) && column && row
    then ret OTSVerify H pubkey msg' sig'
    else ret false.

  (* replace the "row" check with the independent but 
   probabilistically equivalent check "r" *)
  Definition Game2_r :=
    i <-$ [ 0 .. l);
    r <-$ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m);
    k <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a2 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a2;
    column <- negb (ith_element msg i ?= ith_element msg' i);
    if negb (msg' ?= msg) && column && r
    then ret OTSVerify H pubkey msg' sig'
    else ret false. 

  Theorem rnd_bool_uniform : forall x y,
      evalDist ({0,1}) x == evalDist ({0,1}) y. 
  Proof.
    intuition.
    assert (forall x, evalDist (m <-$ { 0 , 1 }^ 1; ret Vector.hd m) x ==
                      evalDist ({0,1}^1) [x]).
    fcf_compute.
    rewrite H0.
    rewrite H0.
    apply uniformity.
  Qed.

  (* these checks have the same probability (are isomorphic) *)
  Lemma Game2_Game2_r :
    Pr[Game2] == Pr[Game2_r].
  Proof.
    unfold Game2, Game2_r.
    fcf_skip.
    (* need to keep sampling of r around *)
    fcf_swap fcf_left.
    fcf_swap fcf_right.
    fcf_skip. 
    destruct x0.
    fcf_swap fcf_left.
    fcf_swap fcf_right.
    fcf_skip.
    destruct x0.
    symmetry.
    destruct (ith_element m x) eqn:R.
    (* want f : {0,1} -> {0,1} such that 
                        (f x0) <-> (Some b ?= Some x0) *)
    eapply (distro_iso_eq (fun x => if b then negb x else x)
            (fun x => if b then negb x else x)); intuition.
    destruct b, x0; simpl; reflexivity.
    destruct b, x0; simpl; reflexivity.
    eapply getSupport_In_Seq.
    instantiate (1:= ((if b then negb x0 else x0)::[])%vector).
    destruct b, x0; simpl; intuition.
    simpl; intuition.
    apply rnd_bool_uniform.

    (* now we have replaced x0 with (f x0) on the LHS *)
    fcf_skip.
    fcf_skip.
    fcf_simp.
    destruct (Some b ?= Some x0) eqn:B.
      (* both conditions are true *)
    rewrite eqb_leibniz in B.
    inversion B. clear B. subst b.
    destruct x0; simpl; reflexivity.
      (* both conditions are false *)
    apply eqb_false_iff in B.
    destruct b, x0; simpl; intuition.

    (* ith_element _ = None is not possible *)
    exfalso.
    apply RndNat_support_lt in H0.
    apply ith_element_safe in R.
    intuition.
    inversion nz_l; omega.
    assumption.
  Qed.
    
  (* Puts game in form of indep_and theorem *)
  Definition Game2_indep :=
    b <-$ (i <-$ [ 0 .. l);
    k <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a2 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a2;
    column <- negb (ith_element msg i ?= ith_element msg' i); 
    (if negb (msg' ?= msg) && column 
     then ret OTSVerify H pubkey msg' sig'
     else ret false));
    r <-$ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m);
    ret (b && r).

  Lemma Game2_r_Game2_indep :
    Pr[Game2_r] == Pr[Game2_indep].
  Proof.
    unfold Game2_r, Game2_indep.
    fcf_inline_first.
    fcf_skip.
    (* need to keep r sampling around *)
    fcf_swap fcf_left.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_swap fcf_left.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_swap fcf_left.
    fcf_inline_first.
    fcf_skip.
    fcf_swap fcf_left.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_swap fcf_right.   
    fcf_skip.
    Local Opaque evalDist.
    destruct (m0 ?= m) eqn:D;
    destruct (negb (ith_element m x ?= ith_element m0 x)) eqn:C;
    simpl; fcf_simp; try reflexivity.

    simpl; fcf_simp.
    destruct x1.
    Local Transparent evalDist.
    rewrite andb_true_r.
    reflexivity.
    rewrite andb_false_r.
    reflexivity.
  Qed.

  Lemma Game1_Game2 : 
   (1/2) * Pr[Game1] == Pr[Game2_indep].
  Proof.
    unfold Game1, Game2_indep.
    (* Now we can apply indep_and *)
    rewrite indep_and.
    rewrite ratMult_comm.
    eapply ratMult_eqRat_compat.
    fcf_skip.
    fcf_irr_l; wftac.
    fcf_compute.
  Qed.

  Theorem step2 : 
      (1/2) * Pr[Game1] == Pr[Game2].
  Proof.
    rewrite Game2_Game2_r.
    rewrite Game2_r_Game2_indep.
    apply Game1_Game2.
  Qed.

 
   (****************    3. Change keys to use y    ********************)  

  (* Need to modify the keys to insert into the public key without 
     altering the relationship between the keys *)

  Definition PrivKeyGenInsert {l : nat} i r n :=
    x <-$ {0,1}^n;
    z <-$ OTSKeyGen_priv n l;
    ret (keyInsert i r x z).

  Theorem PrivKeyGenInsert_equiv : forall l i r n x,
      evalDist (OTSKeyGen_priv n l) x ==
      evalDist (@PrivKeyGenInsert l i r n) x. 
  Proof.
    Local Opaque evalDist. 
    induction l0; intuition;
    unfold PrivKeyGenInsert in *; simpl.
    fcf_irr_r; wftac.
    fcf_simp.
    unfold keyInsert.
    destruct r,i; simpl;
    reflexivity.

    unfold keyInsert.
    destruct i; simpl.
    (* this value will replace one of the sampled values *)
    destruct r; simpl.
      (* swap x with x1 *)
      fcf_swap fcf_right.
      fcf_inline_first.
      fcf_skip.
      fcf_swap fcf_right.
      fcf_skip.
      fcf_inline_first.
      fcf_irr_r; wftac.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      simpl; reflexivity.

      (* swap x with x0 *)
      fcf_skip.
      fcf_inline_first.
      fcf_irr_r; wftac.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      fcf_simp.
      simpl; reflexivity.


      (* now i=/=0 so we are not swapping immediately (use IH) *)
      fcf_swap fcf_right.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.

      (* make z match our IH *)
      assert (evalDist
                (z <-$ OTSKeyGen_priv n0 l0;
                [xi0, xi1]<-2 z; ret (x :: xi0, x0 :: xi1))
                (a, b)
          == (evalDist
                (z <-$ (x0 <-$ {0,1}^n0;
                         k <-$ OTSKeyGen_priv n0 l0;
                         ret keyInsert i r x0 k);
                 [xi0,xi1]<-2 z; ret (x :: xi0, x0 :: xi1))
                (a, b))).
      
      (* we could also fcf_skip all this *)
      eapply evalDist_seq_eq.
      apply IHl0.
      reflexivity.
      rewrite H2.
      
      (* now we have keyInsert on both sides *)
      unfold keyInsert.
      fcf_swap fcf_right.
      fcf_inline_first.
      fcf_skip.
      fcf_inline_first.
      fcf_skip.
      (* on the left, x1 gets inserted into x2 *)
      (* on the right, x2 is the key and then x1 is inserted *)
      destruct x2.
      fcf_ret fcf_right.
      destruct r; simpl; reflexivity.
      Local Transparent evalDist.
   Qed.
      

  Definition KeyGenInsert i r :=
    x <-$ {0,1}^n;
    [prikey,pubkey] <-$2 OTSKeyGen H n l;
    newpri <- keyInsert i r x prikey;
    newpub <- keyInsert i r (H n x) pubkey;
    ret (newpri,newpub).


  (* We just need to maintain the relationship between the keys 
   then can rely on PrivKeyGen_equiv  *)
  Theorem KeyGenInsert_equiv : forall i r x,
      evalDist (OTSKeyGen H n l) x ==
      evalDist (KeyGenInsert i r) x. 
  Proof.
    intuition.
    unfold KeyGenInsert, OTSKeyGen.
    assert (evalDist (z <-$ OTSKeyGen_priv n l;
            [xi0,xi1] <-2 z; ret (xi0,xi1,(map (H n) xi0, map (H n) xi1)))
            (a0,b0,(a,b1)) ==
            (evalDist (z <-$ @PrivKeyGenInsert l i r n;
            [xi0,xi1] <-2 z; ret (xi0,xi1,(map (H n) xi0, map (H n) xi1)))
            (a0,b0,(a,b1)))).
    fcf_skip.
    apply PrivKeyGenInsert_equiv.
    rewrite H0. clear H0.

    unfold PrivKeyGenInsert.
    fcf_inline_first.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.

    revert i r a0 b0 a b1.
    destruct i; intuition.

    destruct r.
    destruct x0.
    specialize (OTS_keygenpriv_keylengths _ _ _ _ H1) as Keys.
    destruct l0,l1; try (
    simpl in Keys;
    inversion nz_l;
    omega).
    destruct n. inversion nz_n; omega.
    unfold keyInsert.
    unfold keyInsertSingle.
    fcf_simp.
    unfold fst.
    unfold snd.
    destruct (map (H (S n0)) (b :: l0)) eqn:M1.
    inversion M1.
    destruct (map (H (S n0)) (b2 :: l1)) eqn:M2.
    inversion M2.
    simpl in M1.
    simpl in M2.
    inversion M1.
    inversion M2.
    simpl.
    reflexivity.

    destruct x0.
    specialize (OTS_keygenpriv_keylengths _ _ _ _ H1) as Keys.
    destruct l0,l1; try (
    simpl in Keys;
    inversion nz_l;
    omega).
    destruct n. inversion nz_n; omega.
    unfold keyInsert.
    unfold keyInsertSingle.
    fcf_simp.
    unfold fst.
    unfold snd.
    destruct (map (H (S n0)) (b :: l0)) eqn:M1.
    inversion M1.
    destruct (map (H (S n0)) (b2 :: l1)) eqn:M2.
    inversion M2.
    simpl in M1.
    simpl in M2.
    inversion M1.
    inversion M2.
    simpl.
    reflexivity.

    destruct x0. 
    destruct r.
   
    specialize (OTS_keygenpriv_keylengths _ _ _ _ H1) as Keys.
    destruct l0,l1; try (
    simpl in Keys;
    inversion nz_l;
    omega).
    destruct n. inversion nz_n; omega.
    unfold keyInsert.
    unfold keyInsertSingle.
    fold (@keyInsertSingle (S n0) i). 
    unfold snd in *.
    unfold fst in *.
    destruct (map (H (S n0)) (b :: l0)) eqn:M1.
    inversion M1.
    destruct (map (H (S n0)) (b2 :: l1)) eqn:M2.
    inversion M2.
    simpl in M1.
    simpl in M2.
    inversion M1.
    inversion M2.
    fcf_simp.
    subst.
    replace (map (H (S n0)) (b2 :: keyInsertSingle i x l1)) with
            (H (S n0) b2 :: keyInsertSingle i (H (S n0) x) (map (H (S n0)) l1)).
    reflexivity.
    simpl.
    f_equal.
    apply keyInsertSingle_map.     
    specialize (OTS_keygenpriv_keylengths _ _ _ _ H1) as Keys.
    destruct l0,l1; try (
    simpl in Keys;
    inversion nz_l;
    omega).
    destruct n. inversion nz_n; omega.
    unfold keyInsert.
    unfold keyInsertSingle.
    fold (@keyInsertSingle (S n0) i). 
    unfold snd in *.
    unfold fst in *.
    destruct (map (H (S n0)) (b :: l0)) eqn:M1.
    inversion M1.
    destruct (map (H (S n0)) (b2 :: l1)) eqn:M2.
    inversion M2.
    simpl in M1.
    simpl in M2.
    inversion M1.
    inversion M2.
    fcf_simp.
    subst.
    replace (map (H (S n0)) (b :: keyInsertSingle i x l0)) with
            (H (S n0) b :: keyInsertSingle i (H (S n0) x) (map (H (S n0)) l0)).
    reflexivity.
    simpl.
    f_equal.
    apply keyInsertSingle_map.
  Qed.

  (* Now we use a keypair with x and H x inserted *)
  (* Note: Game3 is not the one playing the Invert game so it is okay 
   that it knows x. Game3 has a useful distribution for later *)
  Definition Game3 := 
    i <-$ [0..l);
    r <-$ {0,1}; 
    k <-$ KeyGenInsert i r;
    [prikey, pubkey]<-2 k;
    a1 <-$ A1 n l pubkey;
    [msg, state]<-2 a1;
    sig <-$ OTSSign prikey msg;
    a2 <-$ A2 n l (sig, state);
    [msg', sig']<-2 a2;
    column <- negb (ith_element msg i ?= ith_element msg' i);
    row <- negb (ith_element msg i ?= Some r);
    if negb (msg' ?= msg) && column && row 
    then ret OTSVerify H pubkey msg' sig'
    else ret false.

   
  Lemma Game2_Game3 :
    Pr[Game2] == Pr[Game3].
  Proof.
    unfold Game2, Game3.
    fcf_skip.
    fcf_skip.
    fcf_skip.
    apply KeyGenInsert_equiv.
  Qed.

  Theorem step3 :
    Pr[Game2] == Pr[Game3].
  Proof.
    rewrite Game2_Game3.
    reflexivity.
  Qed.

   (******************  4. B uses A1,A2 to invert H  *******************)  

   
  (* B is our constructed adversary which will use A1 and A2 to 
   invert the y that it is given   *)
  Definition B (y : Bvector n) := 
    (* Generate a key *)
    key <-$ @OTSKeyGen H n l;
    [privkey,pubkey] <-2 key;
    
    (* Insert y in pubkey at index (r,i) *)
    i <-$ [0..l);
    r <-$ {0,1};
    invertKey <- keyInsert i r y pubkey;

    (* Give advkey to adversary and get back a message *) 
    [m,state] <-$2 A1 n l invertKey;

    (* Sign the message if we can *)
    if ith_element m i ?= Some r then ret None
    else 
    s <-$ @OTSSign n l privkey m;

    (* Give the sig to the adversary and get back a forgery *)
    x <-$ A2 n l (s,state); 
    [m',s'] <-2 x;
    (* return this no matter what, 1/2l chance of success *)
    ret (nth_error s' i).

  (* Simplification of the Forge game with B as a parameter *)
  Definition B_inverts d :=
    x <-$ {0,1}^n;
    a <-$ OTSKeyGen H n l; 
    [prikey,pubkey] <-2 a;
    i <-$ [ 0 .. l);
    r <-$ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m);
    z <-$ A1 n l (keyInsert i r (H n x) pubkey);
    [m, state]<-2 z;
    s <-$ OTSSign (keyInsert i r x prikey) m;
    x0 <-$ A2 n l (s, state); [_, s']<-2 x0; 
    a0 <- nth_error s' i;
    a1 <-$
    match a0 with
    | Some x' => ret (x', false)
    | None => ret (d, true)
    end; x' <-$ ret fst a1;
    ret ((H n x' ?= H n x) && (negb (ith_element m i ?= Some r))). 
 
  Definition unOption {A : Set} {eqdA : EqDec A}
             (c : Comp (option A)) (default : A) :=
    x <-$ c; 
    match x with 
    | Some x' => ret (x',false)
    | None    => ret (default,true)
    end.
   
  (* Push sampling to the top from B_inverts *)
  Definition GameB d :=
    i <-$ [ 0 .. l);
    r <-$ (m <-$ { 0 , 1 }^ 1; ret Vector.hd m);
    x <-$ {0,1}^n;
    a <-$ OTSKeyGen H n l;
    [prikey, pubkey]<-2 a;
    z <-$ A1 n l (keyInsert i r (H n x) pubkey);
    [m, state]<-2 z;
    s <-$ OTSSign (keyInsert i r x prikey) m;
    x0 <-$ A2 n l (s, state);
    [_, s']<-2 x0;
    a0 <- nth_error s' i;
    a1 <-$
    match a0 with
    | Some x' => ret (x', false)
    | None => ret (d, true)
    end;
    x' <-$ ret fst a1;
    ret ((H n x' ?= H n x) && (negb (ith_element m i ?= Some r))).

  (* Just rearranging *)
  Lemma GameB_B : forall d,
      Pr[GameB d] == Pr[B_inverts d].
  Proof.
    intuition.
    unfold GameB, B_inverts. 
    fcf_at fcf_swap fcf_left 1%nat.
    fcf_swap fcf_left.
    fcf_skip.
    fcf_at fcf_swap fcf_left 1%nat.
    fcf_swap fcf_left.
    fcf_skip.
    fcf_simp.
    fcf_skip.
  Qed.


  (* The crux of the proof *)
  (* This is an inequality for the cases: 
     - A2 returns the same message that it previously queried 
     - Colum or Row are false so our reduction "failed" *)
  Lemma Game3_GameB : forall d, 
    Pr[Game3] <= Pr[GameB d].
  Proof.
    unfold Game3, GameB, KeyGenInsert.
    intuition.

    fcf_skip.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    fcf_skip.
    fcf_simp.
    fcf_skip.
    fcf_simp.
    fcf_skip.
    fcf_skip.
    fcf_simp.

    (* A2 tries to forge the queried message *)
    destruct (m0 ?= m) eqn:Differ.
    unfold negb.
    rewrite andb_false_l.

    destruct (nth_error _);
    unfold fst;
    fcf_compute;
    try reflexivity.

    destruct (negb (ith_element m x ?= Some x0)) eqn:Row.
    destruct (negb (ith_element m x ?= ith_element m0 x)) eqn:Column.
    unfold negb.
    rewrite andb_true_l.

    destruct (nth_error _) eqn:Some;
    unfold fst;
    fcf_simp;
    destruct (OTSVerify _) eqn:Verif;
    try (fcf_compute; reflexivity).

    simpl.
    destruct (EqDec_dec _).
    destruct (EqDec_dec _).
    reflexivity.

    (* if Differ, Row, and Column are true then OTSVerify_spec says 
     that H n b = H n x1 *)
    exfalso.
    intuition.
    apply n0.
    rewrite andb_true_r.

    eapply OTSVerify_spec.
    inversion nz_l.
    eassumption.

    (* we inserted x1 and H n x1 into the keys *)
    instantiate (2:=keyInsert x x0 x1 p).
    instantiate (1:=keyInsert x x0 (H n x1) p0).
    destruct p,p0.
    destruct x2.
    repeat simp_in_support.

    eapply OTS_keygen_uniform_keyInsert.
    assumption.

    (* perhaps we could capture this as a probability and then 
     conclude that it must be negligible in the asymptotic setting *)
    (* but we are happy to use this axiom as a contradiction *)
    eapply A2_successful.
    eassumption.

    eassumption.

    eapply keyValues_keyInsert.
    apply RndNat_support_lt in H0.
    assumption.
    instantiate (1:=p).
    destruct p,p0.
    destruct x2.
    repeat simp_in_support.
    eapply OTS_keygen_uniform;
    apply OTS_keygenpriv_keylengths in H3;
    inversion H3;
    assumption.
    
    assert ((ith_element m0 x ?= Datatypes.Some x0) = true
            \/ (ith_element m0 x ?= Datatypes.Some (negb x0)) = true) as R'.
    apply ith_element_either.
    inversion nz_l; assumption.
    apply RndNat_support_lt; assumption.
    inversion R'.
    assumption.

    assert ((ith_element m x ?= Datatypes.Some x0) = true
            \/ (ith_element m x ?= Datatypes.Some (negb x0)) = true) as R.
    apply ith_element_either.
    inversion nz_l; assumption.
    apply RndNat_support_lt; assumption.
    inversion R.
    exfalso.
    destruct (ith_element m x ?= Datatypes.Some x0) eqn:M.
    unfold negb in Row.
    inversion Row.
    inversion H9.

    rewrite eqb_leibniz in H8.
    rewrite eqb_leibniz in H9.
    rewrite <- H8 in H9.

    destruct (ith_element m x ?= ith_element m0 x) eqn:M.
    unfold negb in Column.
    inversion Column.
    apply eqb_false_iff in M. 
    contradiction.

    fcf_compute.

    (* x is within bounds of s so this can't happen *)
    apply nth_error_None in Some.
    apply RndNat_support_lt in H0.
    apply OTS_verify_length1 in Verif.
    destruct x2.
    specialize (OTS_keygenpriv_keylengths _ _ _ _ H3) as Keys.  
    inversion Keys.
    destruct p,p0.
    rewrite keyInsert_length in Verif.
    repeat simp_in_support.
    rewrite map_length in Verif.
    rewrite <- Verif in Some.
    omega.
    
    (* Column is false *)
    rewrite andb_false_r.
    destruct (nth_error _);
    fcf_compute;
    reflexivity.

    (* Row is false *)
    rewrite andb_false_r. 
    destruct (nth_error _);
    fcf_compute;
    reflexivity.
  Qed.

  (* B_inverts will work as long as the original message's path doesn't 
   touch y (since we don't know x to return a signature) *)
  Lemma B_inverts_Invert : forall d,
      Pr[B_inverts d] <= @Invert_Advantage (Bvector n) (Bvector n) (Rnd n) _ (H n ) (fun y => x <-$ (unOption (B y) d); ret fst x).
  Proof.
    unfold B_inverts, Invert_Advantage, Invert_G, B, unOption.
    intuition.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    fcf_skip.
    fcf_simp.
    fcf_inline_first.
    fcf_skip.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    destruct (ith_element m x1 ?= Some (Vector.hd x2)) eqn:Row.
      unfold negb.
      fcf_irr_l; try apply well_formed_OTSSign.
      fcf_irr_l.
      fcf_simp.
      destruct (nth_error _);
      fcf_simp;
      rewrite andb_false_r;
      fcf_compute;
      reflexivity.
    fcf_inline_first.
    fcf_skip.
    rewrite OTS_sign_untouched.
    reflexivity.
    destruct x0.
    repeat simp_in_support.
    assumption.
    destruct (ith_element m x1 ?= Some (Vector.hd x2)).
    inversion Row.
    unfold negb; reflexivity.

    fcf_inline_first.
    fcf_skip.
    fcf_simp.
    unfold negb.
    destruct (nth_error _);
    fcf_skip;
    rewrite andb_true_r;
    fcf_simp;
    reflexivity.
  Qed.

  Theorem step4 : forall d,
      Pr[Game3] <= Pr[B_inverts d].
  Proof. 
    intuition.
    rewrite Game3_GameB.
    apply eqRat_impl_leRat.
    rewrite GameB_B.
    reflexivity.
  Qed.


    (******************  Final Result   *******************)  


  Definition OTSigForge := (@OTSigForge_Advantage (Msg l) (Sig n) (Keypart n * Keypart n) (Keypart n * Keypart n) _ (OTSKeyGen H n l) OTSSign (OTSVerify H) _ (A1 n l) (A2 n l)).

  Definition Invert d := (@Invert_Advantage (Bvector n) (Bvector n) (Rnd n) _ (H n) (fun y => x <-$ (unOption (B y) d); ret fst x)).

  Theorem Lamport_secure : forall d,   
    (1/2) * (1/l) * OTSigForge <= Invert d.
  Proof.
    intuition.
    rewrite OTSigForge_A_forges.
    rewrite ratMult_assoc.
    rewrite step1.
    rewrite step2.
    rewrite step3.
    rewrite step4.
    rewrite B_inverts_Invert.
    unfold Invert.
    reflexivity.
  Qed.
   



End Lamport.