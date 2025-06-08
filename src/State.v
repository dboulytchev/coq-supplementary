(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Id.
Require Import Coq.Program.Equality.
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
  Proof. induction st.
    dependent destruction SN. dependent destruction SN.
    + dependent destruction SM.
      - reflexivity.
      - contradiction.
    + dependent destruction SM.
      - contradiction.
      - apply (IHst SN SM).  
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. unfold update. constructor. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof. split.
    + intros H. apply neq_id_sym in NEQ. constructor; assumption.
    + intros H. unfold update in H. dependent destruction H.
      - contradiction.
      - assumption.
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. split. 
    - intros H. inversion H.
      apply st_binds_hd. apply st_binds_tl.
      auto.  
      apply update_neq in H6.
      auto. auto.
    - intros H. inversion H.
      apply st_binds_hd. apply st_binds_tl.
      apply H5. apply update_neq.
      auto. auto.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. destruct (Id.id_eq_dec x1 x2).
    - rewrite e in SN.
      specialize (state_deterministic st x2 n1 m SN SM).
      intro H.
      rewrite e; rewrite H.
      constructor.
    - apply update_neq. auto. auto.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. inversion SM.
    - apply st_binds_tl.
      rewrite H3 in NEQ.
      auto. apply update_eq.
    - destruct (id_eq_dec x2 x3).
      + inversion H5.
        * apply st_binds_hd. 
        * symmetry in e. contradiction.
      + apply update_neq. auto.
        apply update_neq. auto.
        apply update_neq in H5. auto.
        auto.
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof. unfold state_equivalence. tauto. Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof. unfold state_equivalence. intros x a. split; intros; apply H; assumption. Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof. unfold state_equivalence. intros. split; intros.
    + apply H2, H1. assumption.
    + apply H1, H2. assumption.
  Qed. 

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof. rewrite HE. apply st_equiv_refl. Qed.
  
End S.
