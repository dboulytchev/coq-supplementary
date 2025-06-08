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
    generalize dependent m.
    induction SN; intros.
      inversion SM; subst.
      reflexivity.
      contradiction.
      inversion SM; subst.
      contradiction.
      apply IHSN. assumption.
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
    unfold update. split.
    intros H. apply st_binds_tl. 
       symmetry. exact NEQ.
       assumption.
    intros H. inversion H.
       rewrite H0 in NEQ. contradiction.
       assumption.
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. 
    specialize id_eq_dec with x1 x2.
    intros [H | H].
    rewrite H. split.
       intros H1. inversion H1.
         apply update_eq.
         contradiction.
      intros H1. inversion H1.
         apply update_eq. 
         contradiction.
    split.
       intros H1. apply update_neq. { symmetry. assumption. }
        apply update_neq in H1. apply update_neq in H1. 
         assumption.
         symmetry. assumption.
         symmetry. assumption.
      intros H1. apply update_neq. { symmetry. assumption. } 
        apply update_neq. { symmetry. assumption. }  
        apply update_neq in H1.
         assumption.
         symmetry. assumption.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [Heq | Hneq].
      rewrite Heq in *. 
      assert (n1 = m) by (apply state_deterministic with (st := st) (x := x2); assumption).
      subst m.
      apply update_eq.
      apply update_neq.
        assumption.
        assumption.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    destruct (id_eq_dec x3 x1) as [Heq1 | Hneq1].
      rewrite Heq1 in *.
      assert (m = n2).
        inversion SM; subst.
        reflexivity.
        contradiction.
      subst m.
      apply update_neq.
      assumption.
        apply update_eq.
      destruct (id_eq_dec x3 x2) as [Heq2 | Hneq2].
        rewrite Heq2 in *.
        assert (m = n1).
          apply update_neq in SM.
          inversion SM; subst.
          reflexivity.
          contradiction.
          symmetry. assumption.
        subst m.
        apply update_eq.
        apply update_neq.
          symmetry. assumption.
          apply update_neq.
             symmetry. assumption.
             apply update_neq in SM.
                apply update_neq in SM.
                   assumption.
                   symmetry. assumption.
                symmetry. assumption.
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
Proof. Abort.

  Lemma st_eval_binds (st: state) (x: id) (n: A) : (st_eval st x = Some n) <-> (st / x => n).
  Proof.
    induction st.
    split.
       intros H. unfold st_eval in H. discriminate.
       intros H. inversion H.
     split.
       intros H. simpl in H. destruct a as [x' a]. destruct (id_eq_dec x' x).
         injection H as H. rewrite e. rewrite H. apply st_binds_hd.
         apply IHst in H. apply st_binds_tl. symmetry. assumption. assumption.
       intros H. inversion H.
         simpl. destruct (id_eq_dec x x).
           reflexivity.
           contradiction.
         simpl. destruct (id_eq_dec id' x).
           rewrite e in H2. contradiction.
           apply IHst. assumption.
  Qed.

  Lemma state_extensional_equivalence_neg : 
    (exists a : A, True) -> ~(forall st st', (forall x z, st/x => z <-> st' / x => z) -> st = st').
  Proof. unfold not. intros [a] state_extensional_equivalence.
    specialize state_extensional_equivalence with ([(Id 0, a); (Id 0, a)]) ([(Id 0, a)]).
    intros. assert (H1: (forall (x : id) (z : A),
     st_binds ([(Id 0, a); (Id 0, a)]) x z <-> st_binds ([(Id 0, a)]) x z)). {
       intros. rewrite <- st_eval_binds. rewrite <- st_eval_binds. simpl. destruct (id_eq_dec (Id 0) x).
        apply iff_refl.
        apply iff_refl.
     }
     apply state_extensional_equivalence in H1. discriminate.
  Qed.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma equiv_update (st st' : state) (id: id) (x: A) (HS: st ~~ st') :
    (st[id <- x]) ~~ (st'[id <- x]).
  Proof. 
    split; intros; destruct (id_eq_dec id x0); 
    inversion H; try congruence; subst;
    try apply st_binds_hd;
    try (apply st_binds_tl; try auto; apply HS; assumption).
  Qed.

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    unfold state_equivalence.
    intros x a.
    apply iff_refl.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    unfold state_equivalence in *.
    intros x a.
    specialize (H x a).
    apply iff_sym. assumption.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    unfold state_equivalence in *.
    intros x a.
    specialize (H1 x a).
    specialize (H2 x a).
    apply iff_trans with (st' / x => a); assumption.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    unfold state_equivalence.
    intros x a.
    rewrite HE.
    apply iff_refl.
  Qed.
End S.
