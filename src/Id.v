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

Notation "n i<= m" := (le_id n m).
Notation "n i>  m" := (gt_id n m).
Notation "n i<  m" := (lt_id n m).

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
Proof. 
  intros id1 id2.
  destruct id1. destruct id2.
  remember (lt_eq_lt_dec n n0). destruct Heqs.
  inversion s. 
  inversion H. left. left. constructor. assumption.
  left. right. subst n. reflexivity.
  right. constructor. assumption.
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof. 
  intros id1 id2.
  destruct id1. destruct id2.
  remember (lt_eq_lt_dec n n0). destruct Heqs.
  inversion s. 
  inversion H. right. constructor. assumption.
  left. right. subst n. reflexivity.
  left. left. constructor. assumption.
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof. 
  intros id1 id2.
  destruct id1. destruct id2.
  remember (lt_eq_lt_dec n n0). destruct Heqs.
  inversion s. inversion H.
  left. constructor. lia.
  left. constructor. lia.
  right. constructor. lia.
Qed.

Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros id1 id2.
  destruct id1. destruct id2.
  remember (eq_nat_dec n n0). destruct Heqs.
  inversion s. left. subst n. constructor.
  right. injection. auto.
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof. 
  intros.
  remember (id_eq_dec x x). destruct s.
  auto. contradiction.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof. 
  intros.
  remember (id_eq_dec x y). destruct s.
  contradiction. reflexivity.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intros. destruct id1. destruct id2.
  induction n as [| n' Hn]; induction n0 as [| n0' Hn0'].
  inversion H. lia.
  inversion H. lia.
  inversion H0. lia.
  inversion H; inversion H0. lia.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof.
  intros. destruct id1. destruct id2.
  inversion H; inversion H0. 
  subst m. subst m0. subst n0. subst n2. lia.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof.
  intros. destruct id1; destruct id2.
  pose proof (le_lt_eq_dec n n0) as [Hl | He]. 
  inversion H. assumption.
  right. apply gt_conv. intuition.
  left. auto.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof. 
  intros. 
  remember (gt_eq_gt_id_dec id1 id2).
  inversion s. inversion H0. auto. 
  subst id1. intuition. auto.
Qed.
    
Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof. 
  intros.
  destruct id1; destruct id2.
  inversion H; inversion H0.
  subst n. subst n0. subst n1. lia.
Qed.
