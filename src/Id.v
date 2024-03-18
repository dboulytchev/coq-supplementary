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
  intros.
  destruct id1 as [n1]. destruct id2 as [n2].
  remember (lt_eq_lt_dec n1 n2). inversion s as [fst | snd].
  - inversion fst.
    + left. left. constructor. assumption.
    + left. right. rewrite H. reflexivity.
  - right. constructor. assumption.
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof.  
  intros.
  destruct id1 as [n1]. destruct id2 as [n2].
  remember (gt_eq_gt_dec n1 n2). inversion s as [fst | snd].
  - destruct fst as [l | r].
    + right. constructor. assumption.
    + left. right. rewrite r. reflexivity.
  - left. left. constructor. assumption.
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof. 
  intros.
  destruct id1 as [n1]. destruct id2 as [n2].
  remember (le_gt_dec n1 n2). inversion s as [fst | snd].
  - left. constructor. assumption.
  - right. constructor. assumption.
Qed.

Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. 
  intros.
  destruct id1 as [n1]. destruct id2 as [n2].
  remember (Nat.eq_dec n1 n2). inversion s as [fst | snd].
  - left. rewrite fst. reflexivity.
  - right. injection. assumption.
Qed.  

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof. intros. remember (id_eq_dec x x). destruct s.
  - reflexivity.
  - contradiction.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof. intros. remember (id_eq_dec x y). destruct s as [fst | snd].
  - contradiction.
  - reflexivity.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intro id1. intro id2.
  destruct id1 as [n1]. destruct id2 as [n2].
  intros. inversion H. subst. inversion H0. subst.
  destruct (Nat.lt_irrefl n1).
  apply (Nat.lt_trans n1 n2 n1). 
  - assumption.
  - assumption.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof.
  intros id1 id2 H1 H2.
  destruct id1 as [n1]. destruct id2 as [n2].
  inversion H1. subst. inversion H2. subst. lia.
Qed.

Lemma lt_iff_gt_id: forall id1 id2 : id,
  id1 i< id2 <-> id2 i> id1.
Proof.
  intros id1 id2.
  destruct id1 as [n1]. destruct id2 as [n2]. split.
  - intros. inversion H. subst. constructor. lia.
  - intros. inversion H. subst. constructor. lia.
Qed.


Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof.
  intros id1 id2.
  destruct (lt_eq_lt_id_dec id1 id2).
  - inversion s.
    + right. apply lt_iff_gt_id. assumption.
    + left. assumption.
  - right. apply lt_iff_gt_id. apply (le_gt_id_false id2 id1) in H. 
    + exfalso. assumption.
    + apply lt_iff_gt_id in l. assumption.
Qed. 

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof.
  intros.
  destruct (lt_eq_lt_id_dec  id1 id2).
  - inversion s.
    + right. apply lt_iff_gt_id. assumption.
    + apply H in H0. exfalso. assumption.
  - left. apply lt_iff_gt_id. assumption.
Qed.
    
Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof.
  intros id1 id2 H1 H2.
  destruct id1 as [n1]. destruct id2 as [n2].
  inversion H1. inversion H2. subst. lia.
Qed.

