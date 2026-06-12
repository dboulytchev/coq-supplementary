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
  (* helper for st_eval_iff_st_binds *)
  Lemma st_eval_to_st_binds : forall (st : state) (x : id) (a : A),
    st_eval st x = Some a -> st / x => a.
  Proof.
    intros st; induction st as [| [x' a'] st' IHst].
    - (* [] *) intros x a H; simpl; discriminate H.
    - (* :: *)
      intros x a H; simpl in H; destruct (id_eq_dec x' x) as [H_eq | H_neq].
      + (* = *)
        subst x'. injection H as H_eq_a. subst a'.
        apply st_binds_hd.
      + (* <> *)
        apply st_binds_tl.
        * congruence. 
        * apply IHst. exact H.
  Qed.

  (* helper for st_eval_iff_st_binds *)
  Lemma st_binds_to_st_eval : forall (st : state) (x : id) (a : A),
    st / x => a -> st_eval st x = Some a.
  Proof.
    intros st x a H; induction H as [st' id y | st' id y id' x' H_neq H_binds IHst].
    - (* hd *) simpl; destruct (id_eq_dec id id) as [H_eq | H_neq].
      + reflexivity.
      + contradiction H_neq. reflexivity.
    - (* tl *) simpl; destruct (id_eq_dec id' id) as [H_eq' | H_neq'].
      + subst id'. contradiction H_neq. reflexivity.
      + exact IHst.
  Qed.

  Lemma st_eval_iff_st_binds : forall (st : state) (x : id) (a : A),
    st_eval st x = Some a <-> st / x => a.
  Proof.
    intros st x a. split.
    - apply st_eval_to_st_binds.
    - apply st_binds_to_st_eval.
  Qed.
  

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
  Proof using Type.
    induction SN;
    inversion SM;
    subst;
    auto;
    contradiction.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    unfold update.
    constructor.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    unfold update.
    split.
    - (* => *)
      intros H.
      apply st_binds_tl with (id':=x2) (x':=n); auto.
    - (* <= *)
      intros H; inversion H; subst; [contradiction | assumption].
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [H_eq | H_neq].
    - (* x1=x2 *)
      subst. split; intro H.
      + assert (m = n2).
        { eapply state_deterministic.
          - exact H.
          - apply update_eq.
        }
        subst. apply update_eq.
      + assert (m = n2).
        { eapply state_deterministic.
          - exact H.
          - apply update_eq.
        }
        subst. apply update_eq.
    - (* x1!=x2 *)
      split; intro H.
      + apply update_neq in H; auto.
        apply update_neq in H; auto.
        apply update_neq; auto.
      + apply update_neq in H; auto.
        apply update_neq; auto.
        apply update_neq; auto.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [H_Eq | H_NotEq].
    - subst.
      assert (m = n1).
      { eapply state_deterministic; eauto. }
      subst.
      apply update_eq.
    - apply update_neq.
      + exact H_NotEq.
      + exact SM.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. 
      destruct (id_eq_dec x3 x1) as [H_eq | H_neq].
  - (* x1=x3 => n2=m *)
    subst. assert (m = n2).
    {
      eapply state_deterministic.
      - exact SM.
      - apply update_eq.
    }
    subst. apply update_neq.
    + exact NEQ.
    + apply update_eq.
  - (* x1!=x3 => (x2=x3 => m=n1) | (m!=n1) *)
    destruct (id_eq_dec x3 x2) as [H_eq_inner | H_neq_inner].
    + subst. assert (m = n1).
      {
        eapply state_deterministic.
        - exact SM.
        - apply update_neq.
          * congruence.
          * apply update_eq.
      }
      subst. apply update_eq.
    + apply update_neq in SM; auto.
      apply update_neq in SM; auto.
      apply update_neq; auto.
      apply update_neq; auto.
  Qed.

  (* not true. proof below *)
  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Theorem state_extensional_equivalence_is_wrong :
    (exists a : A, a = a) -> 
    (exists st st' : state, (forall x z, st / x => z <-> st' / x => z) /\ st <> st').
  Proof.
    intros [a _].
    exists [(Id 1, a)]; exists [(Id 1, a); (Id 1, a)]; split.
    - intros x z; rewrite <- st_eval_iff_st_binds; rewrite <- st_eval_iff_st_binds; simpl.
      destruct (id_eq_dec (Id 1) x) as [H_eq | H_neq].
      + (* = *)
        reflexivity.
      + (* != *)
        reflexivity.
    - intros H_false; discriminate H_false.
  Qed.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    unfold state_equivalence.
    intros x a.
    split; intro H; exact H.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    unfold state_equivalence.
    intros x a.
    split; intro H'; apply H; exact H'.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    unfold state_equivalence.
    intros x a.
    split; intro H.
    - apply H2. apply H1. exact H.
    - apply H1. apply H2. exact H.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    unfold state_equivalence.
    intros x a. (*Show.*)
    rewrite HE. (*Show.*)
    split; intro H; exact H.
  Qed.
  
End S.
