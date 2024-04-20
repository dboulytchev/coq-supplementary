(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Arith Arith.Compare_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Nat.
Require Import Lia.
Require Import Coq.Logic.Decidable.

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
<<<<<<< HEAD
Proof. prove_with lt_eq_lt_dec. Qed.
  
Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof. prove_with gt_eq_gt_dec. Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof. prove_with le_gt_dec. Qed.
=======
Proof. 
  intros id1 id2. 
  destruct id1, id2. 
  remember (lt_eq_lt_dec n n0).
  destruct s. destruct s.
  + left. left. constructor. assumption.
  + left. right. subst n. reflexivity.
  + right. constructor. assumption.
Qed.
  
Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof.
  intros id1 id2.
  destruct id1, id2.
  remember (gt_eq_gt_dec n n0).
  destruct s. destruct s.
  + right. constructor. assumption.
  + left. right. subst n. reflexivity.
  + left. left. constructor. assumption.
Qed. 

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof.
  intros id1 id2.
  destruct id1, id2.
  remember (le_gt_dec n n0).
  destruct s.
  + left. constructor. assumption.
  + right. constructor. assumption.
Qed.

>>>>>>> 09e6753 (Proof some of Id lemmas.)

Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros id1 id2.
  destruct id1, id2.
  remember (eq_nat_decide n n0).
  destruct s.
  + left.
    remember (eq_nat_eq n n0).
    apply e0 in e as e1.
    subst n.
    reflexivity.
  + right. 
    unfold not.
    intro.
    inversion H.
    remember (eq_eq_nat n n0).
    unfold not in n1.
    apply e in H1 as H2.
    apply n1 in H2.
    assumption.
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof. 
  intros T x p q.
  remember (id_eq_dec x x).
  destruct s.
  + reflexivity.
  + contradiction.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof.
  intros T x y p q.
  remember (id_eq_dec x y).
  destruct s; intro.
  + contradiction.
  + reflexivity.
Qed.

Lemma ge_falso : forall n : nat, n > n -> False.
Proof.
  intros n n1.
  remember (nat_compare_gt n n).
  apply i in n1.
  assert (n <= n).
  + constructor.
  + remember (nat_compare_le n n).
    apply i0 in H.
    contradiction.  
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intros id1 id2.
  intro.
  intro.
  inversion H.
  inversion H0.
  destruct id1.
  destruct id2.
  destruct H2.
  destruct H3.
  destruct H5.
  destruct H6.
  inversion H.
  remember (n0 ?= m0).
  symmetry in Heqc.
  destruct c.
  + remember (nat_compare_eq n0 m0).
    apply e in Heqc.
    subst n0.
    subst m1.
    remember (ge_falso m0).
    contradiction.
  + assert (n0 ?= m0 <> Lt).
    - remember (nat_compare_gt n0 m0).
      apply i in H4.
      unfold not.
      admit.
    - admit.
  + admit.  
Admitted.


Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof. admit. Admitted.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof. admit. Admitted.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof. admit. Admitted.
    
Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof. admit. Admitted.
