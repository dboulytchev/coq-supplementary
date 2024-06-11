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

  Lemma neq_comm:  forall (A: Type) (x y: A),
    x <> y <-> y <> x.
  Proof.
    intros x y.
    split; intros H;
    unfold not in *; intros H'; apply H; subst;
    reflexivity.
  Qed.

  Lemma eq_comm : forall (T: Type) (x y: T),
    x = y <-> y = x.
  Proof.
    intros T x y.
    split; intros H; rewrite H; reflexivity.
  Qed.

  Lemma state_R_iff_fn (st: state) (x: id) (n: A) :
    st_eval st x = Some n <-> st_binds st x n.
  Proof.
    split.
    - generalize dependent x.
      generalize dependent n.
      (* TODO reduce duplication *)

      induction st; intros n x.
      + intros F. discriminate F.
      + intros H. simpl in H.

        destruct a as [x' a].
        destruct (id_eq_dec x' x); subst.
        * injection H as H. rewrite H. apply st_binds_hd.
        * apply st_binds_tl.
          { apply neq_comm. assumption. }
          { apply IHst. assumption. }
    - intros H. induction H.
      + simpl.
        apply eq_id.
      + simpl.
        rewrite IHst_binds.
        apply neq_id.
        apply neq_comm.
        assumption.
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
    induction SN; subst.
    - apply state_R_iff_fn in SM.
      simpl in SM.
      destruct (id_eq_dec id id).
      + injection SM.
        trivial.
      + contradiction n. reflexivity.
    - apply state_R_iff_fn in SM;
      simpl in *.
      destruct (id_eq_dec id' id).
      + apply eq_comm in e. apply H in e. destruct e.
      + apply state_R_iff_fn in SM.
        apply IHSN in SM.
        assumption.
  Qed.

  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    unfold update.
    apply state_R_iff_fn.
    simpl.
    destruct id_eq_dec.
    - reflexivity.
    - contradiction n0.
      reflexivity.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split; intros H.
    - unfold update. apply st_binds_tl.
      + apply neq_comm.
        assumption.
      + assumption.
    - unfold update in H.
      apply state_R_iff_fn in H.
      simpl in H.
      destruct (id_eq_dec x2 x1).
      + apply NEQ in e. destruct e.
      + apply state_R_iff_fn. assumption.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    split; intros H.
    - unfold update in *.
      apply state_R_iff_fn in H.
      simpl in H.
      destruct (id_eq_dec x2 x1).
      + injection H as H; subst.
        apply st_binds_hd.
      + apply st_binds_tl.
        { apply neq_comm. assumption. }
        { apply state_R_iff_fn. assumption. }
    - unfold update in *.
      apply state_R_iff_fn in H.
      simpl. simpl in H.
      destruct (id_eq_dec x2 x1); subst.
      { injection H as H; subst. apply st_binds_hd. }
      { apply st_binds_tl .
        + apply neq_comm. assumption.
        +  apply st_binds_tl.
          * apply neq_comm. assumption.
          * apply state_R_iff_fn. assumption.   }
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    unfold update.

    apply state_R_iff_fn.
    apply state_R_iff_fn in SN.
    apply state_R_iff_fn in SM.

    simpl.
    destruct (id_eq_dec x1 x2); subst.
    - rewrite <- SN. rewrite <- SM. reflexivity.
    - assumption.
  Qed.

  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    unfold update in *.

    apply state_R_iff_fn.
    apply state_R_iff_fn in SM.

    simpl in *.

    destruct (id_eq_dec x1 x3) eqn: H1;
    destruct (id_eq_dec x2 x3) eqn: H2;
    subst.

    - injection SM as SM.
      contradiction NEQ.
      reflexivity.
    - assumption.
    - assumption.
    - assumption.
  Qed.

End S.
