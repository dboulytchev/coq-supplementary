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
  Lemma st_not_binds_empty: forall (key: id) (val: A),
    not ([] / key => val).
  Proof.
    intros. unfold not. intros cons. inversion cons.
  Qed.

  Lemma st_binds_equiv_st_eval: forall (st: state) (key: id) (val: A),
    st / key => val <-> st_eval st key = Some val.
  Proof.
    intros. split.
    - intros cons. induction st as [|[key' val'] tl IHst].
      + apply st_not_binds_empty in cons. destruct cons.
      + simpl. destruct (id_eq_dec key' key).
        * f_equal. rewrite e in cons. inversion cons.
          { reflexivity. }
          { congruence. }
        * apply IHst. inversion cons.
          { congruence. }
          { congruence. }
    - intros cons. induction st as [|[key' val'] tl IHst].
      + simpl in cons. discriminate.
      + simpl in cons. destruct (id_eq_dec key' key).
        * injection cons. intros ev. rewrite e. rewrite ev. constructor.
        * constructor.
          { congruence. }
          { apply IHst. apply cons. }
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
  Proof. rewrite st_binds_equiv_st_eval in SN. rewrite st_binds_equiv_st_eval in SM. congruence. Qed.

  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. unfold update. constructor. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof. split.
    - intros cons. constructor.
      + congruence.
      + apply cons.
    - intros cons. unfold update in cons. inversion cons.
      + congruence.
      + congruence.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. split.
    - intros cons. unfold update in cons. inversion cons.
      + apply update_eq.
      + apply update_neq.
        * congruence.
        * apply update_neq in H5.
          { apply H5. }
          { congruence. }
    - intros cons. unfold update. inversion cons.
      + apply update_eq.
      + subst. apply update_neq.
        * congruence.
        * apply update_neq.
          { congruence. }
          { apply H5. }
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. destruct (id_eq_dec x1 x2).
    - subst. assert (n1 = m).
      { apply (state_deterministic st x2 _). auto. apply SM. }
      subst. apply update_eq.
    - apply update_neq.
      + congruence.
      + apply SM.
  Qed.

  Lemma update_eq': forall (st: state) (x: id) (n m: A),
    st [x <- n] / x => m -> n = m.
  Proof. intros. assert (UpdEq: st [x <- n] / x => n).
      { apply update_eq. }
    unfold update in H. unfold update in UpdEq. inversion H.
    - reflexivity.
    - congruence.
  Qed.

  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. destruct (id_eq_dec x1 x3).
  - assert (x2 <> x3). { congruence. } subst. apply update_neq.
    + congruence.
    + apply update_eq' in SM. subst. apply update_eq.
  - apply update_neq in SM.
    + destruct (id_eq_dec x2 x3).
      * subst. apply update_eq' in SM. subst. apply update_eq.
      * apply update_neq in SM.
        { apply update_neq.
          { congruence. }
          { apply update_neq.
            { congruence. }
            { apply SM. }
          }
        }
        { congruence. }
    + congruence.
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. Abort.

  Lemma not_state_extensional_equivalence (NOTEMPTY: exists a: A, True):
    exists (st st': state), (forall x z, st / x => z <-> st' / x => z) /\ st <> st'.
  Proof. destruct NOTEMPTY as [a]. exists ([(Id 0, a)]). exists ((Id 0, a) :: [(Id 0, a)]).
  split.
  - intros. destruct (id_eq_dec (Id 0) x);
    subst; split; intros;
    inversion_clear H0; (constructor + congruence + (inversion H2; congruence)); progress auto.
  - congruence.
  Qed.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof. unfold state_equivalence. intros. reflexivity. Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof. unfold state_equivalence. symmetry. apply H. Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof. unfold state_equivalence. intros x a. transitivity (st' / x => a).
  - apply H1.
  - apply H2.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof. subst. apply st_equiv_refl. Qed.

End S.
