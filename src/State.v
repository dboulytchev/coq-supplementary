(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Export Arith Arith.EqNat.
Require Export Id.

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

  Lemma state_deterministic (st : state) (x : id) (n m : A)
        (SN : st / x => n)
        (SM : st / x => m) :
    n = m.
  Proof.
    induction st as [| [i a] st' IH].
    - inversion SN.
    - inversion SN as [st1 i1 x1 i_eq_i1 x_eq_i | st1 i1 x1 i' x' x_neq_i n_in_st'].
      + inversion SM as [st2 i2 x2 | st2 i2 x2 i1' x1' x_neq_i m_in_st'].
        * apply eq_trans with (a). symmetry. assumption. assumption.
        * symmetry in x_eq_i. contradiction.
      + inversion SM as [st2 i2 x2 i2_eq_i x_eq_i | st2 i2 x2 i1' x1' x_neq'_i m_in_st'].
        * symmetry in x_eq_i. contradiction.
        * apply IH in n_in_st'. assumption. assumption.
  Qed.

  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    unfold update. apply st_binds_hd.
  Qed.

  Lemma update_eq' (st : state) (x : id) (n m : A) :
    st [x <- n] / x => m <-> n = m.
  Proof.
    split.
    - intros H.
      pose proof (update_eq st x n) as H'.
      apply state_deterministic with (n:=n) in H.
      assumption. assumption.
    - intros H. rewrite <- H. apply update_eq.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split.
  - intros H. apply not_eq_sym in NEQ. apply st_binds_tl with (st:=st) (x:=m) (x':=n) in NEQ.
    assumption. assumption.
  - intros H. inversion H.
    + contradiction.
    + assumption.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    split; intros H;
    pose proof (id_eq_dec x1 x2) as [x1_eq_x2 | x1_neq_x2].
    - rewrite -> x1_eq_x2. rewrite -> x1_eq_x2 in H.
      apply update_eq' in H.
      rewrite <- H. apply update_eq.
    - apply not_eq_sym in x1_neq_x2.
      apply update_neq. assumption. 
      apply update_neq in H. apply update_neq in H.
      assumption. assumption. assumption.
    - rewrite -> x1_eq_x2 in H.
      rewrite -> x1_eq_x2.
      apply update_eq' in H.
      rewrite <- H. apply update_eq.
    - apply not_eq_sym in x1_neq_x2.
      apply update_neq. assumption.
      apply update_neq. assumption.
      apply update_neq in H. assumption. assumption.
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof. 
    pose proof (id_eq_dec x1 x2) as [x1_eq_x2 | x1_neq_x2].
    - rewrite <- x1_eq_x2 in SM. rewrite <- x1_eq_x2.
      apply update_eq'. 
      apply state_deterministic with (n:=m) in SN. symmetry.
      assumption. assumption.
    - apply update_neq. assumption. assumption.
  Qed.

  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    pose proof (id_eq_dec x1 x3) as [x1_eq_x3 | x1_neq_x3];
    pose proof (id_eq_dec x2 x3) as [x2_eq_x3 | x2_neq_x3].
    - assert (x2_eq_x1 : x2 = x1). 
      { apply eq_trans with (x3). assumption. symmetry. assumption. }
      contradiction.
    - rewrite -> x1_eq_x3 in SM.
      apply update_eq' in SM.
      apply update_neq. assumption.
      rewrite <- SM. rewrite <- x1_eq_x3. apply update_eq.
    - rewrite <- x2_eq_x3. apply update_eq'.
      apply update_neq in SM. rewrite <- x2_eq_x3 in SM.
      apply update_eq' in SM. assumption. assumption.
    - apply update_neq. assumption. 
      apply update_neq. assumption.
      apply update_neq in SM. 
      apply update_neq in SM.
      assumption. assumption. assumption.
Qed.

End S.
