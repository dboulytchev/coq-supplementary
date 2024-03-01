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

  Fixpoint st_eval (st : state) (x : id) : option A :=
    match st with
    | (x', a) :: st' =>
        if id_eq_dec x' x then Some a else st_eval st' x
    | [] => None
    end.

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
    induction st.
    {
      inversion SN.
    }
    {
      inversion SN.
      {
        rewrite H2 in H0.
        rewrite H3 in H0.
        inversion SM.
        {
          rewrite H6 in H4.
          rewrite H7 in H4.
          rewrite <- H4 in H0.
          inversion H0.
          reflexivity.
        }
        {
          rewrite <- H in H0.
          inversion H0.
          contradiction.
        }
      }
      {
        inversion SM.
        {
          rewrite H5 in H6.
          rewrite H8 in H6.
          rewrite <- H in H6.
          inversion H6.
          contradiction.
        }
        {
          apply IHst.
          apply H4.
          apply H10.
        }
      }
    }
  Qed.

  Lemma eval_binds_eq (st : state) (x : id) :
      (forall n, st_binds st x n <-> st_eval st x = Some n) /\
      ((forall n, ~ (st_binds st x n)) <-> st_eval st x = None).
  Proof.
    split; split.
    + intro H. induction H; simpl.
      - destruct (id_eq_dec id id); [reflexivity | contradiction].
      - destruct (id_eq_dec id' id); [
          subst id; contradiction
        | assumption].
    + intro H. induction st.
      - simpl in H. inversion H.
      - simpl in H. destruct a. destruct (id_eq_dec i x).
        * subst i. inversion H. constructor.
        * constructor; auto; unfold not; unfold not in n0; intro; symmetry in H0; auto.
    + intro H. unfold not in H. induction st.
      - simpl. reflexivity.
      - simpl. destruct a. destruct (id_eq_dec i x).
        * subst i. exfalso. eapply H. constructor.
        * apply IHst. intros n0 H1. eapply H. constructor. unfold not in n. unfold not. intro. subst x. auto. eassumption.
    + intro H. induction st.
      - intro. unfold not. intro. inversion H0.
      - simpl in H. destruct a. destruct (id_eq_dec i x).
        * inversion H.
        * intro. unfold not. intro. unfold not in IHst. eapply IHst.
          assumption.
          inversion H0. subst i. subst id. contradiction. eassumption.
  Qed.

  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. apply st_binds_hd. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split.
    {
      apply st_binds_tl.
      unfold not.
      intro.
      symmetry in H.
      contradiction.
    }
    {
      intro.
      inversion H.
      contradiction.
      apply H6.
    }
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    split.
    {
      intro.
      inversion H.
      apply update_eq.
      inversion H6.
      symmetry in H7.
      contradiction.
      apply st_binds_tl.
      apply H5.
      apply H13.
    }
    {
      intro.
      inversion H.
      apply update_eq.
      apply st_binds_tl.
      apply H5.
      apply st_binds_tl.
      apply H5.
      apply H6.
    }
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2).
    {
      assert (G': n1 = m).
      apply (state_deterministic st x1).
      apply SN.
      rewrite e.
      apply SM.
      rewrite G'.
      rewrite e.
      apply update_eq.
    }
    {
      apply update_neq.
      apply n.
      apply SM.
    }
  Qed.

  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    inversion SM.
    {
      apply update_neq.
      rewrite <- H3.
      apply NEQ.
      apply update_eq.
    }
    inversion H5.
    apply update_eq.

    apply update_neq.
    unfold not.
    intro.
    symmetry in H13.
    contradiction.

    apply update_neq.
    unfold not.
    intro.
    symmetry in H13.
    contradiction.

    apply H12.
  Qed.

End S.


Print update_permute.
