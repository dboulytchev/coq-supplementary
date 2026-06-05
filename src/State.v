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
    revert m SM.
    induction SN; intros m SM.
    - inversion SM; subst; try reflexivity.
      exfalso; auto.
    - inversion SM; subst; try reflexivity.
      + exfalso; auto.
      + apply IHSN. assumption.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    apply st_binds_hd.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    unfold update.
    split; intros H.
    - apply st_binds_tl with (id' := x2) (x' := n).
      + intro Heq. apply NEQ. symmetry. exact Heq.
      + exact H.
    - inversion H; subst.
      + exfalso. apply NEQ. reflexivity.
      + assumption.
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [Heq|Hneq].
    - subst.
      split; intros H.
      + assert (st[x2 <- n1][x2 <- n2] / x2 => n2) by apply update_eq.
        apply state_deterministic with (n := n2) in H; auto.
        subst. apply update_eq.
      + assert (st[x2 <- n2] / x2 => n2) by apply update_eq.
        apply state_deterministic with (n := n2) in H; auto.
        subst. apply update_eq.
    - assert (x2 <> x1) as Hneq'.
      { intro Heq. apply Hneq. symmetry. exact Heq. }
      split; intros H.
      + destruct (update_neq (st[x2 <- n1]) x2 x1 n2 m Hneq') as [_ H1].
        apply H1 in H.
        destruct (update_neq st x2 x1 n1 m Hneq') as [_ H2].
        apply H2 in H.
        destruct (update_neq st x2 x1 n2 m Hneq') as [H3 _].
        apply H3. exact H.
      + destruct (update_neq st x2 x1 n2 m Hneq') as [_ H1].
        apply H1 in H.
        destruct (update_neq st x2 x1 n1 m Hneq') as [H2 _].
        apply H2 in H.
        destruct (update_neq (st[x2 <- n1]) x2 x1 n2 m Hneq') as [H3 _].
        apply H3. exact H.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    unfold update.
    destruct (id_eq_dec x1 x2) as [Heq|Hneq].
    - subst.
      apply state_deterministic with (n := n1) in SM; auto.
      subst. apply st_binds_hd.
    - apply st_binds_tl with (id' := x1) (x' := n1).
      + intro Heq. apply Hneq. symmetry. exact Heq.
      + exact SM.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. 
    specialize id_eq_dec with x2 x3. intros [H | H].
    - rewrite H. rewrite H in SM. inversion SM.
      * rewrite H0 in NEQ. rewrite H in NEQ. contradiction.
      * inversion H6.
        + apply update_eq.
        + contradiction.
    - apply update_neq. assumption. specialize id_eq_dec with x1 x3. intros [H1 | H1].
      * rewrite H1. rewrite H1 in SM. inversion SM.
        + apply update_eq.
        + contradiction.
      * apply update_neq. { assumption. } apply update_neq in SM. apply update_neq in SM.
        + assumption.
        + assumption.
        + assumption.
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Lemma st_eval_binds (st: state) (x: id) (n: A) : (st_eval st x = Some n) <-> (st / x => n).
  Proof.
    induction st.
    - split.
      * intros H. unfold st_eval in H. discriminate.
      * intros H. inversion H.
    - split.
      * intros H. simpl in H. destruct a as [x' a]. destruct (id_eq_dec x' x).
        + injection H as H. rewrite e. rewrite H. apply st_binds_hd.
        + apply IHst in H. apply st_binds_tl. symmetry. assumption. assumption.
      * intros H. inversion H.
        + simpl. destruct (id_eq_dec x x).
          -- reflexivity.
          -- contradiction.
        + simpl. destruct (id_eq_dec id' x).
          -- rewrite e in H2. contradiction.
          -- apply IHst. assumption.
  Qed.

  Lemma state_extensional_equivalence_contra : 
    (exists a : A, True) -> ~(forall st st', (forall x z, st/x => z <-> st' / x => z) -> st = st').
  Proof.
    unfold not. intros [a _] H.
    specialize (H ([(Id 0, a); (Id 0, a)]) ([(Id 0, a)])).
    assert (forall x z, ([(Id 0, a); (Id 0, a)]) / x => z <-> ([(Id 0, a)]) / x => z).
    { intros x z. rewrite <- st_eval_binds, <- st_eval_binds. simpl.
      destruct (id_eq_dec (Id 0) x); split; auto. }
    apply H in H0. discriminate.
  Qed.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    intros x a. split; auto.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    intros x a. split; intros; apply H; auto.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    intros x a. split; intros.
    - apply H2. apply H1. assumption.
    - apply H1. apply H2. assumption.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    subst. apply st_equiv_refl.
  Qed.
  
End S.
