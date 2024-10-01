(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Export Arith Arith.EqNat.
Require Export Id.

From hahn Require Import HahnBase.
Require Import Coq.Program.Equality.

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
    induction SN.
    - inversion SM.
      + reflexivity. 
      + subst. contradiction.
    - inversion SM.
      + subst. contradiction.
      + subst. apply IHSN in H6. apply H6.
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
    - intros H0.
      unfold update.
      apply st_binds_tl.
      + auto.
      + assumption.
    - intros H0.
      unfold update in H0.
      inversion H0.
      + subst. contradiction.
      + subst. assumption.
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. 
    split; intros; dependent destruction st; dependent destruction H.
    - apply st_binds_hd.
    - dependent destruction H0.
      + contradiction.
      + apply st_binds_tl.
        * assumption.
        * assumption.
    - apply st_binds_hd.
    - apply st_binds_tl.
      + assumption.
      + inversion H0; subst.
        * contradiction.
        * assumption.
    - apply st_binds_hd.
    - apply st_binds_tl.
      + assumption.
      + apply st_binds_tl.
        * assumption.
        * assumption.
    - apply st_binds_hd.
    - apply st_binds_tl.
      + assumption.
      + apply st_binds_tl.
        * assumption.
        * assumption.
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. 
    destruct (Id.id_eq_dec x1 x2).
    - subst.
      specialize (state_deterministic st x2 n1 m).
      intros H0.
      rewrite H0.
      constructor.
      + assumption.
      + assumption.
    - apply update_neq.
      + assumption.
      + assumption.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    inversion SM; subst.
    - apply update_neq. 
      + assumption.
      + apply update_eq.
    - inversion H5.
      + apply update_eq.
      + apply update_neq.
        * apply not_eq_sym. assumption.
        * apply update_neq.
          ** apply not_eq_sym. assumption.
          ** assumption.
  Qed.

End S.