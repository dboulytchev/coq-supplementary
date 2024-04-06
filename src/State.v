(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Export Arith Arith.EqNat.
Require Export Id.

(* From hahn Require Import HahnBase. *)

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

  (* State and prove a lemma which claims that st_eval and
     st_binds are actually define the same relation.
   *)

  Lemma st_binds_eq_st_eval (st : state) (id' : id) (x : A) :
    st / id' => x <-> st_eval st id' = Some x.
  Proof.
    split.
(*
    (* That's enough, but overautomated *)
     - intros. induction H; auto.
 *)
    - intros. induction H; simpl.
      + apply eq_id.
      + rewrite neq_id.
        * assumption.
        * unfold not. intro. rewrite H1 in H. contradiction.
    - intros. induction st; simpl.
      + discriminate.
      + destruct a. destruct (id_eq_dec i id').
        * inversion H. rewrite e in H1. rewrite eq_id in H1.
          inversion H1. subst. constructor.
        * inversion H. rewrite neq_id in H1. constructor; auto.
          -- assumption.
  Qed.

  Lemma state_deterministic' (st : state) (x : id) (n m : option A)
    (SN : st_eval st x = n)
    (SM : st_eval st x = m) :
    n = m.
  Proof.
    subst n. subst m. reflexivity.
  Qed.

  Lemma state_deterministic (st : state) (x : id) (n m : A)
    (SN : st / x => n)
    (SM : st / x => m) :
    n = m.
  Proof.
    induction SN; inversion SM.
    + reflexivity.
    + contradiction.
    + subst. contradiction.
    + apply IHSN. apply H6.
  Qed.

  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
  induction st; constructor.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split; intros.
    - apply st_binds_tl.
      * auto.
      * apply H.
    - inversion H; subst.
      + contradiction.
      + apply H6.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    split; intros; inversion H; subst.
    + constructor.
    + apply update_neq in H6. apply update_neq.
      * auto.
      * apply H6.
      * auto.
    + constructor.
    + repeat apply update_neq.
      * auto.
      * auto.
      * apply H6.
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2).
    - subst. unfold update.
      assert (H: n1 = m).
      { apply (state_deterministic st x2 n1 m).
        + apply SN.
        + apply SM. }
      subst. constructor.
    - constructor; auto.
  Qed.

  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    inversion SM; subst.
    - apply update_neq.
      + apply NEQ.
      + apply update_eq.
    - inversion H5; subst.
      + apply update_eq.
      + apply update_neq.
        * auto.
        * apply update_neq.
          -- auto.
          -- assumption.
  Qed.

End S.
