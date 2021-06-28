(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Omega.
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

  Lemma state_deterministic (st : state) (x : id) (n m : A)
        (SN : st / x => n)
        (SM : st / x => m) :
    n = m.
  Proof.
    induction SN; inversion SM.
      { auto. } 
      { exfalso. auto. }
      { exfalso. auto. } 
      { auto. }
  Qed.
 
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    constructor.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split; intro H.
    { constructor. auto. auto. }
    { unfold update in H. inversion H. 
        { exfalso. auto. } 
        { auto. } 
    }
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    split. 
    { 
      intros H. inversion H.
      apply st_binds_hd. apply st_binds_tl.
      auto.  
      apply update_neq in H6.
      auto. auto.
    }
    {
      intros H. inversion H.
      apply st_binds_hd. apply st_binds_tl.
      apply H5. apply update_neq.
      auto. auto.
    }
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (Id.id_eq_dec x1 x2).
    { 
      rewrite e in SN.
      specialize (state_deterministic st x2 n1 m SN SM).
      intro H.
      rewrite e; rewrite H.
      constructor.
    }
    { apply update_neq. auto. auto. }
  Qed.

  Lemma update_binds_eq (st: state) (x: id) (n1 n2: A) :
    st [x <- n2] / x => n1 <-> n1 = n2.
  Proof.
    split; intro H.
    { inversion H. auto. exfalso. auto. }
    { rewrite H. constructor. }
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    inversion SM.
    { 
      apply st_binds_tl.
      rewrite H3 in NEQ.
      auto. apply update_eq.
    }
    { 
      destruct (id_eq_dec x2 x3).
      { 
         inversion H5.
         { apply st_binds_hd. }
         { symmetry in e. contradiction. }
      }
      {
        apply update_neq. auto.
        apply update_neq. auto.
        apply update_neq in H5. auto.
        auto.
      }
    }
  Qed.

End S.
