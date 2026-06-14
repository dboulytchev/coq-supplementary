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
    induction SN; intros m SM.
    - inversion SM; subst.
      + reflexivity.
      + contradiction.
    - inversion SM; subst.
      + contradiction.
      +eauto.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    constructor.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split.
    - intro H.
      constructor; [congruence | assumption].
    - intro H.
      inversion H; subst.
      + contradiction.
      + assumption.
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    destruct (id_eq_dec x2 x1) as [EQ | NEQ].
    - subst.
      split; intro H;
        assert (m = n2) as HM by
          (eapply state_deterministic; [exact H | apply update_eq]);
        subst; apply update_eq.
    - split; intro H.
      + apply (proj2 (update_neq (st [x2 <- n1]) x2 x1 n2 m NEQ)) in H.
        apply (proj2 (update_neq st x2 x1 n1 m NEQ)) in H.
        apply (proj1 (update_neq st x2 x1 n2 m NEQ)).
        exact H.
      + apply (proj2 (update_neq st x2 x1 n2 m NEQ)) in H.
        apply (proj1 (update_neq st x2 x1 n1 m NEQ)) in H.
        apply (proj1 (update_neq (st [x2 <- n1]) x2 x1 n2 m NEQ)).
        exact H.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [EQ | NEQ].
    - subst.
      assert (m = n1) by (eapply state_deterministic; eauto).
      subst.
      apply update_eq.
    - apply (proj1 (update_neq st x1 x2 n1 m NEQ)).
      assumption.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    destruct (id_eq_dec x3 x1) as [EQ1 | NEQ1].
    - subst.
      assert (m = n2) as HM by
        (eapply state_deterministic; [exact SM | apply update_eq]).
      subst.
      apply (proj1 (update_neq (st [x1 <- n2]) x2 x1 n1 n2 NEQ)).
      apply update_eq.
    - destruct (id_eq_dec x3 x2) as [EQ2 | NEQ2].
      + subst.
        apply (proj2 (update_neq (st [x2 <- n1]) x1 x2 n2 m ltac:(congruence))) in SM.
        assert (m = n1) as HM by
          (eapply state_deterministic; [exact SM | apply update_eq]).
        subst.
        apply update_eq.
      + apply (proj2 (update_neq (st [x2 <- n1]) x1 x3 n2 m ltac:(congruence))) in SM.
        apply (proj2 (update_neq st x2 x3 n1 m ltac:(congruence))) in SM.
        apply (proj1 (update_neq (st [x1<- n2]) x2 x3 n1 m ltac:(congruence))).
        apply (proj1 (update_neq st x1 x3 n2 m ltac:(congruence))).
        exact SM.
  Qed.

  (*Looks like incorrect statement: [(x, 42); (x, 52)]  [(x, 42)] ?????*)
  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    unfold state_equivalence.
    intros x a.
    reflexivity.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    unfold state_equivalence in *.
    intros x a.
    specialize (H x a).
    tauto.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    unfold state_equivalence in *.
    intros x a.
    specialize (H1 x a).
    specialize (H2 x a).
    tauto.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    subst.
    apply st_equiv_refl.
  Qed.
  
End S.
