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
    induction SN as [sn1 x1 n1 | sn2 x2 n2 x2' n2'].
    - inversion_clear SM.
      + reflexivity.
      + contradict H. reflexivity.
    - assert ((sn2) / x2 => m) as H0. 
      { inversion SM. 
        + contradiction H. auto.
        + assumption. }
      apply (IHSN H0).
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
    split. 
    - intro H.
      remember (st_binds_tl st x1 m x2 n) as P.
      assert (x1 <> x2) as NEQ2. { auto. }
      pose proof (P NEQ2) as PNEQ.
      apply (PNEQ H).
    - intro H.
      inversion H.
      + contradict NEQ. assumption.
      + assumption.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    split.
    - intro H. 
      remember (id_eq_dec x1 x2) as P.
      destruct P as [P1 | P2].
      + assert ((((st) [x2 <- n1]) [x2 <- n2]) / x1 => n2) as H0.
        { rewrite <- P1. 
          apply update_eq. }
        assert (m = n2) as N2eqM. 
        { set (st0 := (((st) [x2 <- n1]) [x2 <- n2])).
          fold st0 in H.
          fold st0 in H0.
          apply (state_deterministic st0 x1 m n2 H H0). }
          rewrite <- N2eqM.
          rewrite <- P1.
          apply update_eq.
      + apply update_neq in H. 
        apply update_neq in H. 
        apply update_neq. 
        auto. auto. auto. auto.
    - intro H.
      remember (id_eq_dec x1 x2) as P.
      destruct P as [P1 | P2].
      + assert (((st) [x2 <- n2]) / x1 => n2) as H0.
        { rewrite <- P1. 
          apply update_eq. }
        assert (m = n2) as N2eqM. 
        { set (st0 := ((st) [x2 <- n2])).
          fold st0 in H.
          fold st0 in H0.
          apply (state_deterministic st0 x1 m n2 H H0). }
          rewrite <- N2eqM.
          rewrite <- P1.
          apply update_eq.
      + apply update_neq in H. 
        apply update_neq. auto. 
        apply update_neq. 
        auto. auto. auto.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. 
    remember (id_eq_dec x1 x2) as P.
    destruct P as [P1 | P2].
    - rewrite <- P1. rewrite <- P1 in SM.
      remember (state_deterministic st x1 m n1 SM SN) as E.
      rewrite <- E.
      apply update_eq.
    - apply update_neq.
      + assumption.
      + assumption.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. 
    remember (id_eq_dec x1 x3) as P.
    destruct P as [P1 | P2].
    - rewrite <- P1 in SM.
      assert (m = n2) as MeqN2.
      { remember (update_eq ((st) [x2 <- n1]) x1 n2) as S.
        set (st0 := ((st) [x2 <- n1]) [x1 <- n2]).
        fold st0 in SM. fold st0 in S.
        apply (state_deterministic st0 x1 m n2 SM S). }
      rewrite <- MeqN2.
      rewrite <- P1.
      apply update_neq.
      assumption.
      apply update_eq.
    - remember (id_eq_dec x2 x3) as P.
      destruct P as [O1 | O2].
      + rewrite <- O1 in SM.
        apply update_neq in SM.
        rewrite <- O1.
        assert (m = n1) as MeqN1. 
        { remember (update_eq st x2 n1) as S.
          apply (state_deterministic ((st) [x2 <- n1]) x2 m n1 SM S). }
        rewrite <- MeqN1.
        apply update_eq.
        auto.
      + apply update_neq. assumption.
        apply update_neq. assumption.
        apply update_neq in SM.
        apply update_neq in SM.
        assumption. assumption. assumption.
Qed.

End S.
