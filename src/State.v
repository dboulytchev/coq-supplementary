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
    induction SN; intros m SM; inversion SM; subst; try reflexivity; try congruence.
    apply IHSN. assumption.
  Qed.
  
  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    unfold update. apply st_binds_hd.
  Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split; intro H.
    - unfold update. apply st_binds_tl.
      + congruence.
      + exact H.
    - unfold update in H. inversion H; subst;
        first [ assumption | (exfalso; apply NEQ; reflexivity) ].
  Qed.
  
  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    destruct (id_eq_dec x2 x1) as [E | NE].
    - subst. split; intro H.
      + assert (H1 : m = n2).
        { exact (state_deterministic _ _ _ _ H (update_eq _ _ _)). }
        subst. apply update_eq.
      + assert (H1 : m = n2).
        { exact (state_deterministic _ _ _ _ H (update_eq _ _ _)). }
        subst. apply update_eq.
    - split; intro H.
      + apply (proj1 (update_neq st x2 x1 n2 m NE)).
        apply (proj2 (update_neq st x2 x1 n1 m NE)).
        apply (proj2 (update_neq (update st x2 n1) x2 x1 n2 m NE)).
        exact H.
      + apply (proj1 (update_neq (update st x2 n1) x2 x1 n2 m NE)).
        apply (proj1 (update_neq st x2 x1 n1 m NE)).
        apply (proj2 (update_neq st x2 x1 n2 m NE)).
        exact H.
  Qed.
  
  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [E | NE].
    - subst.
      assert (H1 : n1 = m) by exact (state_deterministic _ _ _ _ SN SM).
      subst. apply update_eq.
    - apply (proj1 (update_neq st x1 x2 n1 m NE)). exact SM.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    destruct (id_eq_dec x3 x1) as [E1 | NE1].
    - subst x3.
      assert (Hm : m = n2).
      { exact (state_deterministic _ _ _ _ SM (update_eq _ _ _)). }
      subst m.
      apply (proj1 (update_neq (update st x1 n2) x2 x1 n1 n2 NEQ)).
      apply update_eq.
    - assert (NE1' : x1 <> x3) by (intro E; apply NE1; symmetry; exact E).
      apply (proj2 (update_neq (update st x2 n1) x1 x3 n2 m NE1')) in SM.
      destruct (id_eq_dec x3 x2) as [E2 | NE2].
      + subst x3.
        assert (Hm : m = n1).
        { exact (state_deterministic _ _ _ _ SM (update_eq _ _ _)). }
        subst m.
        apply update_eq.
      + assert (NE2' : x2 <> x3) by (intro E; apply NE2; symmetry; exact E).
        apply (proj2 (update_neq st x2 x3 n1 m NE2')) in SM.
        apply (proj1 (update_neq (update st x1 n2) x2 x3 n1 m NE2')).
        apply (proj1 (update_neq st x1 x3 n2 m NE1')).
        exact SM.
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof.
    (* Эта лемма в таком виде ложна.
       Контрпример: при A, имеющем элемент a, и x : id берём
         st  = [(x, a); (x, a)]  и  st' = [(x, a)].
       Отношения st_binds у них совпадают (второе вхождение x затенено,
       так как st_binds_tl требует id <> id'), но списки различны.
       Верно лишь утверждение о state_equivalence (см. ниже). *)
  Abort.

  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
    unfold state_equivalence. intros x a. split; intro H; exact H.
  Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
    unfold state_equivalence in *. intros x a.
    specialize (H x a). destruct H as [H1 H2].
    split; assumption.
  Qed.

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
    unfold state_equivalence in *. intros x a. split; intro H.
    - apply (proj1 (H2 x a)). apply (proj1 (H1 x a)). exact H.
    - apply (proj2 (H1 x a)). apply (proj2 (H2 x a)). exact H.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
    subst. apply st_equiv_refl.
  Qed.
  
End S.