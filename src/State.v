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
  
  Lemma state_deterministic (st : state) (x : id) (n m : A)   
    (SN : st / x => n)
    (SM : st / x => m) :
    n = m. 
  Proof. 
    intros.
    apply st_eval_binds in SN.
    apply st_eval_binds in SM.
    assert (H: Some n = Some m).
      { apply (state_deterministic' st x (Some n) (Some m) SN SM). }
    injection H. intros. assumption.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. 
    apply st_eval_binds. simpl. destruct (id_eq_dec x x).
    - reflexivity.
    - contradiction.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof. 
    intros. split.
    - intros H. apply st_binds_tl. 
      * symmetry. assumption.
      * assumption.
    - intros H. inversion H.
      * rewrite H0 in NEQ. contradiction.
      * assumption.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. 
    specialize id_eq_dec with x1 x2.
    intros [H | H].
    - rewrite H. split.
      * intros H1. inversion H1.
        + apply update_eq.
        + contradiction.
      * intros H1. inversion H1.
        + apply update_eq. 
        + contradiction.
    - split.
      * intros H1. apply update_neq. { symmetry. assumption. }
        apply update_neq in H1. apply update_neq in H1. 
        + assumption.
        + symmetry. assumption.
        + symmetry. assumption.
      * intros H1. apply update_neq. { symmetry. assumption. } 
        apply update_neq. { symmetry. assumption. }  
        apply update_neq in H1.
        + assumption.
        + symmetry. assumption.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    specialize id_eq_dec with x1 x2.
    intros [H | H].
    - rewrite H in SN. specialize state_deterministic with st x2 n1 m. intros H1. apply H1 in SN. 
      * rewrite SN. rewrite H. apply update_eq. 
      * apply SM.
    - apply update_neq.
      * apply H.
      * apply SM.
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

  Lemma state_extensional_equivalence_contra : 
    (exists a : A, True) -> ~(forall st st', (forall x z, st/x => z <-> st' / x => z) -> st = st').
  Proof. unfold not. intros [a] state_extensional_equivalence.
    specialize state_extensional_equivalence with ([(Id 0, a); (Id 0, a)]) ([(Id 0, a)]).
    intros. assert (H1: (forall (x : id) (z : A),
     st_binds ([(Id 0, a); (Id 0, a)]) x z <-> st_binds ([(Id 0, a)]) x z)). {
       intros. rewrite <- st_eval_binds. rewrite <- st_eval_binds. simpl. destruct (id_eq_dec (Id 0) x).
       - apply iff_refl.
       - apply iff_refl.
     }
     apply state_extensional_equivalence in H1. discriminate.
  Qed.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof. unfold state_equivalence. intros. apply iff_refl. Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof. unfold state_equivalence. intros. apply iff_sym. apply H. Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof. 
    unfold state_equivalence. intros. apply iff_trans with (B := (st'/x => a)).
    - apply H1.
    - apply H2.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof. rewrite HE. apply st_equiv_refl. Qed.

  Lemma equiv_update (st st' : state) (id: id) (x: A) (HS: st ~~ st') :
    (st[id <- x]) ~~ (st'[id <- x]).
  Proof. 
    split; intros; destruct (id_eq_dec id x0); 
    inversion H; try congruence; subst;
    try apply st_binds_hd;
    try (apply st_binds_tl; try auto; apply HS; assumption).
  Qed.
  
End S.
