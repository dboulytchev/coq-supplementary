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
  Proof. 
    intros. induction SN; inversion SM.
    - reflexivity.
    - intuition.
    - contradiction H. auto.
    - intuition.
  Qed.
    
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. 
    intros. apply st_binds_hd.
  Qed. 

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof. 
    intros. split.
    - intro. induction st. 
      apply st_binds_tl; intuition. 
      apply st_binds_tl; auto.
    - intro. inversion H. intuition. intuition.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. 
    destruct (id_eq_dec x1 x2); split.
    - rewrite <- e. intro. 
      pose proof (st_binds_hd (st [x1 <- n1]) x1 n2). 
      pose proof (state_deterministic (st [x1 <- n1] [x1 <- n2]) x1 m n2).
      pose proof (H1 H H0).
      pose proof (st_binds_hd st x1 n2). 
      rewrite -> H2. auto.
    - rewrite <- e. intro.
      pose proof (st_binds_hd st x1 n2).
      pose proof (state_deterministic (st [x1 <- n2]) x1 m n2).
      pose proof (H1 H H0).
      pose proof (st_binds_hd (st [x1 <- n1]) x1 n2).
      rewrite -> H2. auto.
    - intro.
      pose proof (update_neq (st [x2 <- n1]) x2 x1 n2).
      assert(x1 <> x2 <-> x2 <> x1). { split. auto. auto. }
      inversion H1. pose proof (H2 n). pose proof ((H0 m) H4). 
      inversion H5. pose proof (H7 H).
      apply st_binds_tl. auto. pose proof (update_neq st x2 x1 n1 m). 
      pose proof (H9 H4). inversion H10. pose proof (H12 H8). auto.
    - intro. 
      pose proof (update_neq (st [x2 <- n1]) x2 x1 n2).
      assert(x1 <> x2 <-> x2 <> x1). { split. auto. auto. }
      inversion H1. pose proof (H2 n).
      pose proof (update_neq (st [x2 <- n2]) x2 x1 n1). 
      pose proof ((H5 m) H4). inversion H6. pose proof (H7 H).
      apply st_binds_tl. auto. pose proof (update_neq st x2 x1 n1 m).
      pose proof (H10 H4). inversion H11. 
      pose proof (update_neq st x2 x1 n2 m). pose proof (H14 H4). inversion H15. 
      pose proof (H17 H). pose proof (H12 H18). auto.
    Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. 
    destruct (id_eq_dec x1 x2).
    - rewrite <- e. pose proof (state_deterministic st x1 n1 m). replace x2 in SM. 
      intuition. rewrite <- H. apply update_eq.
    - apply update_neq. auto. auto.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. admit. Admitted.

End S.
