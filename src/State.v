(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Export Arith Arith.EqNat.
Require Export Id.

From hahn Require Import HahnBase.

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
    induction st as [| [id' a'] st' IH'].
    - inversion SN.
    - inversion SN; subst; clear SN.
      all: inversion SM; subst.
      + reflexivity.
      + contradiction.
      + contradiction.
      + now apply IH'.
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
    unfold update.
    split; intro H.
    {
      simpl. apply st_binds_tl.
      - auto.
      - assumption.
    }

    inversion H; subst; clear H.
    - contradiction.
    - assumption.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    unfold update. split; intros H.
    - inversion H; subst; clear H; [apply st_binds_hd | apply st_binds_tl].
      + assumption.
      + inversion H6; subst.
        * contradiction.
        * assumption.
    - inversion H; subst; clear H; [apply st_binds_hd | apply st_binds_tl].
      + assumption.
      + apply st_binds_tl; assumption.
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    remember (id_eq_dec x1 x2) as s.
    destruct s.
    {
      subst.
      remember (state_deterministic st x2 n1 m) as e.
      specialize (e SN SM) as e'.
      subst.
      constructor.
    }
    {
      constructor; auto.
    }
  Qed.

  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    remember (id_eq_dec x3 x2) as s.
    destruct s.
    {
      subst.
      remember (((st) [x1 <- n2])).
      inversion SM; subst.
      - contradiction.
      - inversion H5; subst; [constructor | contradiction].
    }
    {
      constructor.
      - assumption.
      - inversion SM; subst.
        + constructor.
        + constructor.
          * assumption.
          * inversion H5; subst; [contradiction | assumption].
    }
  Qed.
End S.
