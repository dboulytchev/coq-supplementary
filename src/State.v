(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Init.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.

  Variable A : Set.
  
  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).
  
  (* Functional version of binding-in-a-state relation *)
  Fixpoint st_eval (st : state) (x : id) : option A :=
    match st with
    | (x', a) :: st' =>
        if id_eq_dec x' x then Some a else st_eval st' x
    | [] => None
    end.
 
  (* State a prove a lemma which claims that st_eval and
     st_binds are actually define the same relation.
  *)

  Lemma state_deterministic' (st : state) (x : id) (n m : option A)
    (SN : st_eval st x = n)
    (SM : st_eval st x = m) :
    n = m.
  Proof using Type.
    subst n. subst m. reflexivity.
  Qed.
  
  Lemma state_deterministic (st : state) (x : id) (n m : A)   
    (SN : st / x => n)
    (SM : st / x => m) :
    n = m. 
  Proof.
    intros. simpl.
    induction SN.
    - inversion SM.
      * auto.
      * exfalso. auto.
    - inversion SM.
      * exfalso. auto.
      * apply IHSN. simpl. assumption.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    intros.
    constructor.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    intros.
    split.
    - intro. simpl.
      constructor. auto. assumption.
    - intro. simpl.
      unfold update in H. simpl. inversion H.
        * exfalso. auto.
        * assumption.
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. 
    intros.
    split.
    - intro. simpl.
      inversion H.
      * constructor.
      * apply update_neq.
        + auto.
        + apply update_neq in H6; auto.
    - intro. simpl.
      inversion H.
      * constructor.
      * constructor.
        + auto.
        + apply update_neq. simpl. auto. auto.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. 
    intros. simpl.
    destruct (id_eq_dec x1 x2).
    - rewrite e in SN. 
      specialize (state_deterministic st x2 m n1 SM SN).
      simpl. intro. simpl.
      rewrite -> e.
      rewrite -> H.
      apply update_eq.
    - apply update_neq; auto.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    intros.
    destruct (id_eq_dec x1 x3).
    - rewrite e in SM.
      remember (update_eq (st [x2 <- n1]) x3 n2).
      specialize (state_deterministic (update (st) [x2 <- n1] x3 n2) x3 n2 m s SM).
      auto.
      intro. simpl.
      rewrite H. rewrite e.
      apply update_neq.
      + rewrite <- e. auto.
      + apply update_eq.
    - destruct (id_eq_dec x2 x3).
      + rewrite e.
        apply update_neq in SM.
        * rewrite e in SM.
          specialize (update_eq st x3 n1). intro. simpl.
          specialize (state_deterministic (st [x3 <- n1]) x3 n1 m H SM). intro. simpl.
          rewrite H0.
          apply update_eq.
        * auto.
      + apply update_neq in SM; auto.
        apply update_neq in SM; auto.
        apply update_neq; auto.
        apply update_neq; auto.
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof.
    destruct st.
    - destruct st'.
      + auto.
      + destruct p.
        specialize (H i a).
        inversion H. simpl.
        specialize (update_eq st' i a).
        intro. simpl.
        apply H1 in H2.
        destruct H2.
        * 
  Abort.
  
  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    intros. unfold "~~". tauto.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    intros. unfold "~~". intros.
    split.
    - intros. simpl.
      apply H.
      apply H0.
    - intros. simpl.
      apply H.
      apply H0.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    intros. 
    unfold "~~". simpl. intros. simpl. split.
    - intros. simpl.
      apply H2.
      apply H1.
      apply H.
    - intros. simpl.
      apply H1.
      apply H2.
      apply H.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    intros.
    unfold "~~". split; rewrite HE; auto.
  Qed.
  
End S.
