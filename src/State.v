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
 
  (* The functional and relational lookups agree, including shadowing. *)
  Lemma st_eval_binds (st : state) (x : id) (a : A) :
    st_eval st x = Some a <-> st / x => a.
  Proof.
    induction st as [| [y b] st IH]; simpl.
    - split; intro H; [discriminate | inversion H].
    - destruct (id_eq_dec y x) as [EQ | NEQ].
      + subst. split; intro H.
        * injection H as H. subst. constructor.
        * inversion H; subst; [reflexivity | contradiction].
      + split; intro H.
        * apply st_binds_tl; [congruence | now apply IH].
        * inversion H; subst; [contradiction | now apply IH].
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
    intros. induction SN.
    - inversion SM; subst; congruence.
    - inversion SM; subst; [congruence |].
      apply IHSN; assumption.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. apply st_binds_hd. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split; intro H.
    - apply st_binds_tl; [congruence | assumption].
    - inversion H; subst; [congruence | assumption].
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [EQ | NEQ].
    - subst. split; intro H.
      + assert (m = n2) by (eapply state_deterministic; [exact H | apply st_binds_hd]).
        subst. constructor.
      + assert (m = n2) by (eapply state_deterministic; [exact H | apply st_binds_hd]).
        subst. constructor.
    - split; intro H.
      + assert (N : x2 <> x1) by congruence.
        apply (proj1 (update_neq st x2 x1 n2 m N)).
        apply (proj2 (update_neq (st[x2 <- n1]) x2 x1 n2 m N)) in H.
        apply (proj2 (update_neq st x2 x1 n1 m N)) in H. exact H.
      + assert (N : x2 <> x1) by congruence.
        apply (proj1 (update_neq (st[x2 <- n1]) x2 x1 n2 m N)).
        apply (proj2 (update_neq st x2 x1 n2 m N)) in H.
        apply (proj1 (update_neq st x2 x1 n1 m N)) in H. exact H.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [EQ | NEQ].
    - subst. assert (n1 = m) by (eapply state_deterministic; eauto).
      subst. apply st_binds_hd.
    - apply st_binds_tl; [congruence | assumption].
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    destruct (id_eq_dec x3 x1) as [EQ | N1].
    - subst. inversion SM; subst; [| congruence].
      apply st_binds_tl; [congruence | constructor].
    - destruct (id_eq_dec x3 x2) as [EQ | N2].
      + subst. assert (m = n1) by
            (eapply state_deterministic; [exact SM | apply st_binds_tl; [exact NEQ | constructor]]).
        subst. apply st_binds_hd.
      + assert (N1' : x1 <> x3) by congruence.
        assert (N2' : x2 <> x3) by congruence.
        apply (proj1 (update_neq (st[x1 <- n2]) x2 x3 n1 m N2')).
        apply (proj2 (update_neq (st[x2 <- n1]) x1 x3 n2 m N1')) in SM.
        apply (proj2 (update_neq st x2 x3 n1 m N2')) in SM.
        now apply (proj1 (update_neq st x1 x3 n2 m N1')) in SM.
  Qed.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  (* This original claim is false for states represented as lists:
     [(x, a)] and [(x, a); (x, a)] have identical bindings but are
     different lists. Its statement is intentionally left unchanged. *)
  Lemma state_extensional_equivalence (st st' : state)
        (H : forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Lemma state_extensional_counterexample (x : id) (a : A) :
    (forall y z, st_binds ((x, a) :: nil) y z <->
                 st_binds ((x, a) :: (x, a) :: nil) y z) /\
    (x, a) :: nil <> (x, a) :: (x, a) :: nil.
  Proof.
    split.
    - intros y z. repeat rewrite <- st_eval_binds. simpl.
      destruct (id_eq_dec x y); reflexivity.
    - discriminate.
  Qed.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof. intros x a. tauto. Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof. intros x a. specialize (H x a). tauto. Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof. intros x a. specialize (H1 x a). specialize (H2 x a). tauto. Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof. subst. apply st_equiv_refl. Qed.
  
End S.
