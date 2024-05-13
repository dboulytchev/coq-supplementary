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
  Proof. induction st as [| st'].
  - inversion SN.
  - destruct st;
    inversion SN; inversion SM. subst.
    + inversion H4. reflexivity.
    + subst. inversion H. symmetry in H1. contradiction.
    + subst. inversion H6. contradiction.
    + specialize (IHst H4 H10). assumption.
    + subst. inversion SM.
      * reflexivity.
      * contradiction.
    + subst. inversion SM.
      * reflexivity.
      * contradiction.
    + subst. inversion H6. contradiction.
    + specialize (IHst H4 H10). assumption.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. constructor. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof. split; intros.
  - constructor.
    + auto.
    + assumption.
  - inversion H.
    + contradiction.
    + assumption.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. split.
  - intros. inversion H. subst.
    + constructor.
    + constructor.
      * apply H5.
      * inversion H6. subst. contradiction. subst. apply H13.
  - intros. inversion H; subst.
    + constructor.
    + inversion H; subst. constructor. constructor. assumption. 
      constructor. assumption. assumption.
Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. destruct (id_eq_dec x1 x2).
    - rewrite e. specialize (state_deterministic st x2 n1 m) as spec.
      rewrite e in SN. apply spec in SN.
      + rewrite SN. constructor.
      + assumption.
    - constructor. auto. assumption.
Qed.  
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. destruct (id_eq_dec x3 x2).
    - rewrite e. inversion SM; subst.
      + contradiction.
      + inversion H5; subst.
        * constructor.
        * contradiction.
    - constructor.
      + assumption.
      + inversion SM. subst. constructor. constructor.
        * apply H4.
        * subst. inversion H5. subst. contradiction. assumption.
Qed.

End S.
