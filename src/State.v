(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
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
    induction SN.
    - inversion SM. subst. reflexivity. subst. contradiction.
    - inversion SM.
      + subst. contradiction.
      + subst. apply IHSN. assumption.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. 
    unfold update.
    apply st_binds_hd.
  Qed.


  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    unfold update. split.
    - intros. apply st_binds_tl.
      + symmetry. assumption.
      + assumption.
    - intros. inversion H. subst.
      + contradiction.
      + subst. assumption.
  Qed.

  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. 
    split.
    - intros. inversion H. subst.
      + 
  Abort.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. 
    destruct (id_eq_dec x1 x2).
    - rewrite <- e in SM.
      rewrite <- e. 
      unfold update.
      remember (state_deterministic st x1 n1 m SN SM).
      rewrite e0. apply st_binds_hd.
    - apply update_neq.
      + assumption.
      + assumption.
  Qed.

  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    unfold update. unfold update in SM.
    destruct (id_eq_dec x1 x3).
    - rewrite e in SM. inversion SM. subst.
      + apply update_neq.
        * assumption.
        * apply st_binds_hd.
      + subst. congruence.
    - apply update_neq in SM.
      + inversion SM. subst.
        * apply st_binds_hd.
        * subst. apply st_binds_tl.
          -- assumption.
          -- apply update_neq.
            ++ assumption.
            ++ assumption.
            + assumption.
  Qed.
          

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. 
    destruct st.
  Abort.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    unfold state_equivalence.
    intros. split.
    - intros. apply H.
    - intros. apply H.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof. 
    unfold state_equivalence in H.
    unfold state_equivalence.
    intros. split.
    - intros H'.  apply H. assumption.
    - intros H'. apply H. assumption.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof. 
    unfold state_equivalence in H1.
    unfold state_equivalence in H2.
    unfold state_equivalence.
    intros. split.
    - intros. apply H2. apply H1. assumption.
    - intros. apply H1. apply H2. assumption.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof. 
    unfold state_equivalence.
    intros. split.
    - intros. rewrite <- HE. assumption.
    - intros. rewrite HE. assumption.
  Qed.
  
End S.
