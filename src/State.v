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
    revert m SM.
    induction SN; intros m SM; inversion SM; subst.
    - reflexivity.
    - congruence.
    - congruence.
    - apply IHSN; assumption.
  Qed.

  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    unfold update. constructor.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    unfold update.
    split; intro H.
    - apply st_binds_tl.
      + intro Heq. apply NEQ. symmetry. exact Heq.
      + exact H.
    - inversion H; subst.
      + exfalso. apply NEQ. reflexivity.
      + assumption.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [Heq | Hneq].
    - subst x1. unfold update. split; intro H.
      + inversion H; subst.
        * constructor.
        * congruence.
      + inversion H; subst.
        * constructor.
        * congruence.
    - assert (Hneq' : x2 <> x1) by (intro Heq; apply Hneq; symmetry; exact Heq).
      split; intro H.
      + apply (proj1 (update_neq st x2 x1 n2 m Hneq')).
        apply (proj2 (update_neq st x2 x1 n1 m Hneq')).
        apply (proj2 (update_neq (st [x2 <- n1]) x2 x1 n2 m Hneq')).
        exact H.
      + apply (proj1 (update_neq (st [x2 <- n1]) x2 x1 n2 m Hneq')).
        apply (proj1 (update_neq st x2 x1 n1 m Hneq')).
        apply (proj2 (update_neq st x2 x1 n2 m Hneq')).
        exact H.
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [Heq | Hneq].
    - subst x2.
      assert (n1 = m) as Heq by (apply state_deterministic with (st := st) (x := x1); assumption).
      subst m. apply update_eq.
    - apply (update_neq st x1 x2 n1 m Hneq). exact SM.
  Qed.

  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    assert (NEQ' : x1 <> x2) by (intro Heq; apply NEQ; symmetry; exact Heq).
    destruct (id_eq_dec x3 x1) as [Heq1 | Hneq1].
    - subst x3.
      assert (Hm : m = n2).
      { unfold update in SM. inversion SM; subst.
        - reflexivity.
        - congruence. }
      subst m.
      apply (proj1 (update_neq (st [x1 <- n2]) x2 x1 n1 n2 NEQ)).
      apply update_eq.
    - destruct (id_eq_dec x3 x2) as [Heq2 | Hneq2].
      + subst x3.
        assert (Hm : m = n1).
        { apply (proj2 (update_neq (st [x2 <- n1]) x1 x2 n2 m NEQ')) in SM.
          unfold update in SM. inversion SM; subst.
          - reflexivity.
          - congruence. }
        subst m.
        apply update_eq.
      + assert (Hx1x3 : x1 <> x3) by (intro Heq; apply Hneq1; symmetry; exact Heq).
        assert (Hx2x3 : x2 <> x3) by (intro Heq; apply Hneq2; symmetry; exact Heq).
        apply (proj1 (update_neq (st [x1 <- n2]) x2 x3 n1 m Hx2x3)).
        apply (proj1 (update_neq st x1 x3 n2 m Hx1x3)).
        apply (proj2 (update_neq st x2 x3 n1 m Hx2x3)).
        apply (proj2 (update_neq (st [x2 <- n1]) x1 x3 n2 m Hx1x3)).
        exact SM.
  Qed.

  (* This statement is false in general: e.g. for A = nat, the states
     [(Id 0, 1); (Id 0, 2)] and [(Id 0, 1)] induce the same st_binds
     relation (the shadowed second binding is never observable) but are
     not equal as lists. Verified by explicit counterexample; several
     independent solutions of this assignment also leave this as Abort. *)
  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    unfold state_equivalence. intros x a. reflexivity.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    unfold state_equivalence in *. intros x a. symmetry. apply H.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    unfold state_equivalence in *. intros x a. split; intro Hb.
    - apply H2. apply H1. exact Hb.
    - apply H1. apply H2. exact Hb.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    unfold state_equivalence. subst. intros x a. reflexivity.
  Qed.
  
End S.
