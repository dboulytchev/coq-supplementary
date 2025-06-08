(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Export Arith Arith.EqNat.
Require Export Id.

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
    - inversion SM; subst.
      + reflexivity.
      + contradiction.
    - inversion SM; subst.
      + contradiction.
      + apply IHSN. 
        assumption. 
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
    split. 
    - intros.
      unfold update.
      apply st_binds_tl.
      + apply not_eq_sym. 
        assumption.
      + assumption.
    
    - intros.
      unfold update.
      inversion H; subst.
      + contradiction NEQ. 
        reflexivity.
      + assumption.
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. 
    split.
    - intros.
      unfold update.
      inversion H; subst.
      + apply st_binds_hd.
      + apply st_binds_tl.
        * assumption.
        * apply update_neq in H6; auto.
  - intros.
    unfold update.
    inversion H; subst.
    + apply st_binds_hd.
    + apply st_binds_tl.
      * assumption.
      * apply update_neq; auto.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    unfold update.
    destruct (id_eq_dec x1 x2) as [Heq | Hneq].
    - subst.
      assert (n1 = m) by (eapply state_deterministic; eauto).
      subst.
      apply st_binds_hd.
    - apply st_binds_tl; auto.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. 
    inversion SM; subst.
    - apply update_neq.
      + auto.
      + apply update_eq.
    - inversion H5; subst.
      + apply update_eq.
      + apply update_neq.
        * auto.
        * apply st_binds_tl; 
          assumption.
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Lemma state_extensional_equivalence_counterexample:
    (exists a: A, True) -> exists (st st' : state), 
      (forall x z, st / x => z <-> st' / x => z) /\ st <> st'.
  Proof.
    intros.
    destruct H.
    exists [(Id 0, x); (Id 0, x)].
    exists [(Id 0, x)].
    split.
    - split.
      + intros.
        inversion H0; subst.
        * apply st_binds_hd.
        * assumption.
      + intros. 
        inversion H0; subst.
        * apply st_binds_hd.
        * apply st_binds_tl; assumption.
    - discriminate.
  Qed.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof. 
    unfold state_equivalence.
    split; intros; assumption.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof. 
    unfold state_equivalence.
    split; intros; apply H; assumption.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof. 
    unfold state_equivalence.
    split; intros.
    - apply H2.
      apply H1. 
      assumption.
    - apply H1.
      apply H2.
      assumption. 
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof. 
    unfold state_equivalence.
    split; intros.
    - subst. assumption.
    - subst. assumption.
  Qed.
End S.
