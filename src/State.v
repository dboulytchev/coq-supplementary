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
 
  Lemma state_bind_eq (st : state) (x : id) (n : A) :
  (st_eval st x = Some n) <-> (st / x => n).
  Proof.
    split.
    - intros. induction st.
      * unfold st_eval in H. inversion H. 
      * destruct a as [k v]. destruct (id_eq_dec k x).
        + rewrite e. rewrite e in H. unfold st_eval in H. rewrite eq_id in H.
          inversion H. apply st_binds_hd.
        + apply st_binds_tl. auto. unfold st_eval in H. rewrite neq_id in H. apply IHst. apply H. auto. 
    - intros. induction st.
      * unfold st_eval in H. inversion H. 
      * destruct a as [k v]. destruct (id_eq_dec k x).
        + rewrite e. rewrite e in H. inversion H. unfold st_eval. rewrite eq_id. auto. contradiction.
        + inversion H. contradiction. unfold st_eval. rewrite neq_id. apply IHst. auto. auto.
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
  Proof. 
    rewrite <- state_bind_eq in SN.
    rewrite <- state_bind_eq in SM.
    specialize (state_deterministic' _ _ _ _ SN SM). intros. inversion H. auto. 
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. 
    unfold update. specialize (st_binds_hd st x n). auto.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split.
    - intros. unfold update. apply st_binds_tl; auto.
    - intros. unfold update in H. inversion H. contradiction. auto.
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    repeat rewrite <- state_bind_eq. simpl. destruct (id_eq_dec x1 x2).
    - rewrite e. repeat rewrite eq_id. apply iff_refl.
    - repeat rewrite neq_id; auto. apply iff_refl.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    repeat rewrite <- state_bind_eq. simpl. destruct (id_eq_dec x1 x2).
    - rewrite e in SN. specialize (state_deterministic _ _ _ _ SN SM). intros. rewrite H. auto.
    - rewrite -> state_bind_eq. auto.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    rewrite <- state_bind_eq in SM. simpl in SM. 
    repeat rewrite <- state_bind_eq. simpl. destruct (id_eq_dec x2 x3); destruct (id_eq_dec x1 x3).
    - rewrite e in NEQ. rewrite  e0 in NEQ. contradiction.
    - auto.
    - auto.
    - auto.
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  (** this is false. Let try approve this in next lemma*)
  Proof. admit. Admitted.

Lemma not_state_extensional_equivalence :
 (exists a : A, a = a) -> (exists st st' : state,
         (forall x z, st / x => z <-> st' / x => z) /\ st <> st').
  Proof.
    intros.
    destruct H as [a _].
    exists ((Id 0, a)::nil).
    exists ((Id 0, a)::(Id 0, a)::nil).
    split.
    - intros.
      specialize (update_shadow nil x (Id 0) a a z). 
      intros us. repeat unfold update in us. symmetry. auto.
    - unfold not. intros. inversion H.
  Qed.


  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    unfold state_equivalence. intros.  apply iff_refl.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof. 
    unfold state_equivalence. unfold state_equivalence in H. symmetry. auto.
  Qed.



  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof. 
    unfold state_equivalence. unfold state_equivalence in H1. unfold state_equivalence in H2.
    intros x a.
    apply (iff_trans (H1 x a) (H2 x a)).
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    rewrite HE. apply st_equiv_refl.
  Qed.
  
End S.
