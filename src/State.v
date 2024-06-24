(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Export Arith Arith.EqNat.
From semantics Require Export Id.

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
 
  (* State and prove a lemma which claims that st_eval and
     st_binds actually define the same relation.
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
  Proof. induction SN as [|? ? ? ? ? ? ? IH].
  { inversion SM.
    - reflexivity.
    - subst. contradiction. }
  { inversion SM as [st2 id2 x2 H0 Hid'eq | st2 id2 x2 id'2 x'2 Hidneq Hevm].
    - symmetry in Hid'eq. contradiction.
    - subst. apply IH. apply Hevm. }
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. unfold update. apply st_binds_hd. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof. unfold update. split; intros H.
    { apply st_binds_tl with (st:=st) (x:=m) (id:=x1) (id':=x2) (x':=n).
      - symmetry. apply NEQ.
      - apply H. }
    { inversion H.
      - contradiction.
      - apply H6. }
  Qed.

  Ltac imm_replace expr replacement :=
    replace expr with replacement; [|reflexivity].
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. split; unfold update; intros H.
    { inversion H.
      { subst. apply update_eq. }
      { subst. apply st_binds_tl. apply H5.
        rewrite update_neq with (st:=st) (x1:=x1) (x2:=x2) (m:=m) (n:=n1).
        - unfold update. assumption.
        - symmetry. assumption. } }
    { inversion H.
      { subst. apply update_eq. }
      { subst. apply update_neq. auto.
        imm_replace (st_binds ((x2, n1) :: st) x1 m) (st [x2 <- n1] / x1 => m).
        rewrite <- update_neq; auto. } }
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. destruct (id_eq_dec x1 x2).
    { subst. apply state_deterministic with (n:=m) in SN; [|assumption]. rewrite <- SN.
      apply update_eq. }
    { rewrite <- update_neq; assumption. }
(*inversion SN.
    { subst. replace_def (((x1, n1) :: st0) [x1 <- n1]) ((st0) [x1 <- n1] [x1 <- n1]).
      rewrite update_shadow. assumption. }
    { rewrite H1. clear H1. subst x. *)
  Qed.

  Lemma binds_eq : forall st x n m, st [x <- n] / x => m -> n = m.
  Proof.
    intros. set (Hnm := state_deterministic _ _ _ _ (update_eq (st) x n) H).
    assumption.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    destruct (id_eq_dec x3 x1) as [Heq31|Hneq31].
      { subst. replace (update st x2 n1) with ((x2, n1)::st) in SM; [|reflexivity].
        apply binds_eq in SM. apply update_neq; [assumption|]. subst. constructor. }
      { destruct (id_eq_dec x3 x2) as [Heq32|Hneq32].
        { subst. apply update_neq in SM; [|auto]. apply binds_eq in SM. subst.
          apply update_eq. }
        { repeat (apply update_neq; [auto|]).
          repeat (rewrite <- update_neq in SM; [|auto]). assumption. } }
  Qed.

End S.
