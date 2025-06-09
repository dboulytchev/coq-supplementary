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
Proof.
  intros T x p q.
  destruct (id_eq_dec x x) as [H | H].
  - reflexivity.
  - contradiction H. reflexivity.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof.
  intros T x y p q H_neq.
  destruct (id_eq_dec x y) as [H_eq | H_neq'].
  - contradiction H_neq.
  - reflexivity.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
 id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intros id1 id2 H1 H2.
  destruct id1 as [n1], id2 as [n2].
  inversion H1 as [n1' n2' H1']. subst.
  inversion H2 as [n2'' n1'' H2']. subst.
  lia.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
 id2 i<= id1 -> id2 i> id1 -> False.
Proof.
  intros id1 id2 H_le H_gt.
  destruct id1 as [n1], id2 as [n2].
  inversion H_le as [n2' n1' H_le']. subst.
  inversion H_gt as [n2'' n1'' H_gt']. subst.
  lia.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id,
 id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof.
  intros.
  destruct id1 as [n1], id2 as [n2].
  destruct (eq_nat_dec n1 n2) as [H1 | H2].
  - left. rewrite H1. reflexivity.
  - right. inversion H. apply gt_conv. lia.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
 id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof.
  intros id1 id2 H_neq.
  destruct id1 as [n1], id2 as [n2].
  assert (n1 <> n2) as H_nat_neq.
  { intro contra. apply H_neq. rewrite contra. reflexivity. }
  destruct (lt_eq_lt_dec n1 n2) as [[H_lt | H_eq] | H_gt].
  - right. constructor. assumption.
  - contradiction H_nat_neq.
  - left. constructor. assumption.
Qed.

Lemma eq_gt_id_false : forall id1 id2 : id,
 id1 = id2 -> id1 i> id2 -> False.
Proof.
  intros id1 id2 H_eq H_gt.
  rewrite H_eq in H_gt.
  destruct id2 as [n].
  inversion H_gt as [n1 n2 H_gt']. subst.
  lia.
Qed.