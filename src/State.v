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

  Lemma state_deterministic (st : state) (x : id) (n m : A)
        (SN : st / x => n)
        (SM : st / x => m) :
    n = m.
  Proof. induction st.
    - inversion SN.
    - inversion SN.
      + inversion SM.
        * rewrite <- H3. rewrite <- H7. 
          destruct H0. auto. inversion H4. reflexivity.
        * subst a. subst id. inversion H. revert H6.
          subst x. contradiction.
      + inversion SM.
        * subst a. subst id0. inversion H6.
          revert H2. subst x. contradiction.
        * auto. 
  Qed.
    
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. intros. apply st_binds_hd. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof. intros. split. 
    - intros. apply st_binds_tl. auto. assumption.
    - intros. inversion H. 
      + contradiction.
      + assumption.
  Qed. 

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. 
    intros. remember (id_eq_dec x1 x2). destruct s.
    - split.
      + intros. inversion H. 
        * apply update_eq.
        * contradiction.
      + intros. inversion H.
        * apply update_eq.
        * contradiction.
    - split.
      + intros. inversion H.
        * subst x1. contradiction.
        * inversion H6.
          ** revert H2. subst x1. contradiction.
          ** apply st_binds_tl. 
            *** assumption.
            *** assumption.
      + intros. inversion H.
        * subst x1. contradiction.
        * apply st_binds_tl.
          ** assumption.
          ** apply st_binds_tl.
            *** assumption.
            *** assumption.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. 
    intros. remember (id_eq_dec x1 x2). destruct s.
    - subst x1. remember (state_deterministic st x2 n1 m SN SM). 
      subst n1. apply (update_eq st x2 m).
    - apply st_binds_tl. 
      + auto.
      + assumption.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    intros. remember (id_eq_dec x1 x3). destruct s.
    - inversion SM.
      + rewrite <- e. apply st_binds_tl. 
        * auto.
        * apply (update_eq st x1 m).
      + subst x3. contradiction.
    - remember (id_eq_dec x2 x3). destruct s.
      + inversion SM.
        * contradiction.
        * subst x2. remember (update_eq st x3 n1).
          remember (state_deterministic ((st)[x3 <- n1]) x3 n1 m s H5).
          rewrite -> e. apply (update_eq ((st) [x1 <- n2]) x3 m).
      + apply st_binds_tl. 
        * auto.
        * apply st_binds_tl.
          ** auto.
          ** inversion SM.
            ++ contradiction.
            ++ inversion H5.
              -- contradiction.
              -- assumption.
  Qed.

End S.
