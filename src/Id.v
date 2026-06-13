(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Lia.

Inductive id : Type :=
  Id : nat -> id.
             
Reserved Notation "m i<= n" (at level 70, no associativity).
Reserved Notation "m i>  n" (at level 70, no associativity).
Reserved Notation "m i<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) i<= (Id m)
where "n i<= m" := (le_id n m).   

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) i< (Id m)
where "n i< m" := (lt_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) i> (Id m)
where "n i> m" := (gt_id n m).   

Ltac prove_with th :=
  intros; 
  repeat (match goal with H: id |- _ => destruct H end); 
  match goal with n: nat, m: nat |- _ => set (th n m) end;
  repeat match goal with H: _ + {_} |- _ => inversion_clear H end;
  try match goal with H: {_} + {_} |- _ => inversion_clear H end;
  repeat
    match goal with 
      H: ?n <  ?m |-  _                + {Id ?n i< Id ?m}  => right
    | H: ?n <  ?m |-  _                + {_}               => left
    | H: ?n >  ?m |-  _                + {Id ?n i> Id ?m}  => right
    | H: ?n >  ?m |-  _                + {_}               => left
    | H: ?n <  ?m |- {_}               + {Id ?n i< Id ?m}  => right
    | H: ?n <  ?m |- {Id ?n i< Id ?m}  + {_}               => left
    | H: ?n >  ?m |- {_}               + {Id ?n i> Id ?m}  => right
    | H: ?n >  ?m |- {Id ?n i> Id ?m}  + {_}               => left
    | H: ?n =  ?m |-  _                + {Id ?n =  Id ?m}  => right
    | H: ?n =  ?m |-  _                + {_}               => left
    | H: ?n =  ?m |- {_}               + {Id ?n =  Id ?m}  => right
    | H: ?n =  ?m |- {Id ?n =  Id ?m}  + {_}               => left
    | H: ?n <> ?m |-  _                + {Id ?n <> Id ?m}  => right
    | H: ?n <> ?m |-  _                + {_}               => left
    | H: ?n <> ?m |- {_}               + {Id ?n <> Id ?m}  => right
    | H: ?n <> ?m |- {Id ?n <> Id ?m}  + {_}               => left

    | H: ?n <= ?m |-  _                + {Id ?n i<= Id ?m} => right
    | H: ?n <= ?m |-  _                + {_}               => left
    | H: ?n <= ?m |- {_}               + {Id ?n i<= Id ?m} => right
    | H: ?n <= ?m |- {Id ?n i<= Id ?m} + {_}               => left
    end;
  try (constructor; assumption); congruence.

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 i< id2} + {id1 = id2} + {id2 i< id1}.
Proof. prove_with lt_eq_lt_dec. Qed.
  
Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof. prove_with gt_eq_gt_dec. Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof. prove_with le_gt_dec. Qed.

Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. prove_with Nat.eq_dec. Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof. intros. destruct (id_eq_dec x x).
  - reflexivity.
  - assert (H: x = x). { reflexivity. } unfold not in n. apply n in H. contradiction.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof. intros T x y p q H. destruct (id_eq_dec x y). 
  - unfold not in H. rewrite e in H. assert False.
    * apply H. reflexivity.
    * contradiction.
  - reflexivity.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intros n m H1 H2. 
  inversion H1 as [n1 m1 H3 H4 H5].
  inversion H2 as [n2 m2 H6 H7 H8].
  rewrite <- H4 in H8. injection H8 as H8.
  rewrite <- H5 in H7. injection H7 as H7.
  rewrite H7 in H6. rewrite H8 in H6.
  specialize Nat.lt_asymm with n1 m1 as H9. 
  unfold gt in H3. unfold gt in H6. apply H9 in H6. unfold not in H6. apply H6. apply H3.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof. 
  intros id1 id2 H1 H2.
  inversion H1 as [n1 m1 H3 H4 H5].
  inversion H2 as [n2 m2 H6 H7 H8].
  rewrite <- H4 in H7. injection H7 as H7.
  rewrite <- H5 in H8. injection H8 as H8.
  rewrite H7 in H6. rewrite H8 in H6.
  specialize Nat.le_ngt with n1 m1 as H9. 
  apply H9 in H3. unfold not in H3. unfold gt in H6. apply H3. apply H6.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof. 
  intros [n] [m] H. 
  destruct (n =? m) eqn:E.
  - apply Nat.eqb_eq in E. left. rewrite E. reflexivity.
  - apply Nat.eqb_neq in E. right. inversion H.
    apply le_lt_eq_dec in H2. destruct H2.
    * apply gt_conv. unfold gt. assumption. 
    * rewrite e in E. contradiction.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof. 
  intros id1 id2 H.
  unfold not in H.
  specialize lt_eq_lt_id_dec with id1 id2. intros [[H1|H1]|H1].
  - right. inversion H1. apply gt_conv. unfold gt. assumption.
  - apply H in H1. contradiction.
  - left. inversion H1. apply gt_conv. unfold gt. assumption.
Qed.
    
Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof. 
  intros [n] [m] H1 H2.
  inversion H2 as [n2 m2 H3 H4 H5].
  inversion H1.
  specialize Nat.lt_irrefl with m as H6. 
  rewrite H0 in H3. unfold gt in H3. 
  apply H6. apply H3.
Qed.
