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
  Proof. induction SN.
    inversion SM. reflexivity. contradiction.
    inversion SM. remember (eq_sym H0). contradiction. remember (IHSN H6). exact e.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. apply st_binds_hd. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof. split. apply st_binds_tl. auto. intros. inversion H. contradiction. exact H6. Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. split.
    intros. inversion H.
      apply st_binds_hd.
      inversion H6.
        remember (eq_sym H7). contradiction.
        apply st_binds_tl. exact H5. exact H13.
    intros. inversion H.
      apply st_binds_hd.
      apply st_binds_tl. exact H5. apply st_binds_tl. exact H5. exact H6.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. remember (id_eq_dec x1 x2). inversion s.
    subst. remember (state_deterministic st x2 n1 m SN SM). subst. apply st_binds_hd.
    apply st_binds_tl. auto. exact SM.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. remember (id_eq_dec x1 x3). inversion s.
    subst. apply st_binds_tl. auto. inversion SM. apply st_binds_hd. contradiction.
    remember (id_eq_dec x2 x3). inversion s0.
      subst. inversion SM. contradiction. inversion H6. apply st_binds_hd. contradiction.
      inversion SM. contradiction. inversion H7. contradiction. apply st_binds_tl. exact H13. apply st_binds_tl. exact H6. exact H14.
  Qed.

End S.
