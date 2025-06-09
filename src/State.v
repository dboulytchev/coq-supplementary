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
    - inversion SM.
      + reflexivity.
      + contradiction.
    - inversion SM.
      + subst. contradiction.
      + apply IHSN. assumption.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    apply st_binds_hd.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split.
    - apply st_binds_tl. symmetry. assumption.
    - intro HLeft. inversion HLeft.
      + subst. contradiction.
      + assumption.  
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    split.
    - intro HLeft. inversion HLeft.
      + apply st_binds_hd.
      + apply st_binds_tl.
        * assumption.
        * apply update_neq in H5.
          ** assumption. 
          ** symmetry. assumption. 
    - intro HLeft. inversion HLeft.
      + apply st_binds_hd.
      + apply update_neq.
        * symmetry. assumption.
        * apply st_binds_tl.
          ** assumption.
          ** assumption.    
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2).
    - subst. destruct (state_deterministic _ _ _ _ SN SM). apply update_eq.
    - apply update_neq. 
      + assumption.
      + assumption. 
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    inversion SM.
    - subst. apply update_neq.
      + assumption.
      + apply update_eq.
    - subst. inversion H5.
      + apply st_binds_hd.
      + apply st_binds_tl.
        * assumption.
        * apply update_neq.
          ** symmetry. assumption.
          ** assumption.         
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Theorem state_extensional_equivalence_false : (exists a: A, True) -> exists (st st' : state), (forall x z, st / x => z <-> st' / x => z) /\ st <> st'.
  Proof.
    intros.
    destruct H.
    exists [(Id 0, x); (Id 0, x)].
    exists [(Id 0, x)].
    split.
    - split.
      + intros. inversion H0.
        * apply st_binds_hd.
        * subst. assumption.
      + intros. inversion H0.
        * apply st_binds_hd.
        * subst. apply st_binds_tl. assumption. assumption.
    - discriminate. 
  Qed.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    unfold state_equivalence.
    split.
    - intro Hleft. assumption.
    - intro HLeft. assumption. 
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    unfold state_equivalence. 
    symmetry. 
    apply H.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    unfold state_equivalence.
    unfold state_equivalence in H1, H2.
    intros. 
    rewrite H1. 
    apply H2.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    subst. 
    apply st_equiv_refl.
  Qed.
  
End S.
