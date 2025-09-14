(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Lia.

Inductive id : Type :=
  Id : nat -> id.

Check Id 70.

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
Proof. 
  destruct id1.
  destruct id2.
  remember (Nat.eq_dec n n0).
  destruct s. 
  {
    left.
    rewrite e.
    reflexivity. 
  }
  {
    right.
    unfold not in *.
    intro. 
    inversion H.
    apply n1 in H1.
    assumption.
  }
Qed.  

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof. 
  intros.
  destruct (id_eq_dec x x).
  { reflexivity. }
  { contradiction. }
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof.
  intros.
  destruct (id_eq_dec x y).
  {  contradiction.  }
  {  reflexivity.    }
Qed.


Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof. 
  intros [n] [m] H1 H2.
  inversion H1.
  inversion H2.
  apply Nat.lt_asymm in H3.
  apply H3 in H6.
  contradiction.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof. 
  intros [n] [m] H1 H2.
  inversion H1.
  inversion H2.
  apply Nat.lt_nge in H6.
  apply H6 in H3.
  contradiction.
Qed.

SearchPattern (forall n m, n <= m -> { _ } + { _ }). 
(* le_lt_eq_dec *)
Search (_ > _).

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof. 
  intros [n] [m] H1.
  destruct (n =? m) eqn:E.
  { apply Nat.eqb_eq in E. left. rewrite E. reflexivity. }
  { apply Nat.eqb_neq in E. right. inversion H1. apply le_lt_eq_dec in H2.
  destruct H2. 
    - apply gt_conv. unfold gt. assumption.  
    - apply E in e. contradiction. 
} Qed.


Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof. 
  intros [n] [m] H.
  destruct (lt_eq_lt_id_dec (Id n) (Id m)) as [[H1 | H2] | H3].
  - right. apply gt_conv. unfold gt. inversion H1. assumption.
  - apply H in H2. contradiction.
  - left. apply gt_conv. unfold gt. inversion H3. assumption.
Qed. 
    
Check (Nat.lt_irrefl).

Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof. 
  intros [n] [m] H1 H2.
  inversion H2.
  inversion H1.
  subst.
  apply Nat.lt_irrefl in H3.
  contradiction.
Qed.

