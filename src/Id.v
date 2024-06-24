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

Lemma le_id_le : forall n m, (Id n) i<= (Id m) -> n <= m.
Proof.
  intros n m H. inversion_clear H. assumption.
Qed.

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) i< (Id m)
where "n i< m" := (lt_id n m).   

Lemma lt_id_lt : forall n m, (Id n) i< (Id m) -> n < m.
Proof.
  intros n m H. inversion_clear H. assumption.
Qed.

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) i> (Id m)
where "n i> m" := (gt_id n m).

Lemma gt_id_gt : forall n m, (Id n) i> (Id m) -> n > m.
Proof.
  intros n m H. inversion_clear H. assumption.
Qed.

Lemma eq_id_eq : forall n m, (Id n) = (Id m) <-> n = m.
Proof.
  intros n m. split; intros H.
  - inversion H. reflexivity.
  - subst. reflexivity.
Qed.

Lemma lt_gt_id_switch : forall id1 id2, id1 i< id2 <-> id2 i> id1.
Proof.
  intros id1 id2. destruct id1, id2. split; intros H; inversion_clear H; constructor; lia.
Qed.

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
  destruct (id_eq_dec x x) as [Heq | Hneq].
  { reflexivity. }
  { exfalso. apply Hneq. reflexivity.  }
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof.
  intros T x y p q. intros Hneq.
  destruct (id_eq_dec x y) as [Heq | _].
  * exfalso. apply Hneq. apply Heq.
  * reflexivity.
Qed.

Ltac to_number_and_solve := intros id1 id2; destruct id1; destruct id2; intros H12 H21;
  inversion_clear H12; inversion_clear H21; lia.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof. to_number_and_solve. Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof. to_number_and_solve. Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof.
  intros id1 id2. intros H. destruct (lt_eq_lt_id_dec id1 id2) as [[Hlt12 | Heq] | Hlt21].
  - right. apply lt_gt_id_switch. assumption.
  - left. assumption.
  - right. destruct id1, id2. inversion_clear H. inversion_clear Hlt21. lia.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof.
  intros id1 id2 H. destruct (lt_eq_lt_id_dec id1 id2) as [[Hlt12 | Heq] | Hlt21].
  - right. rewrite <- lt_gt_id_switch. assumption.
  - contradiction.
  - left. rewrite <- lt_gt_id_switch. assumption.
Qed.
    
Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof.
  intros id1 id2. intros Heq. intros Hgt. subst.
  destruct id2. apply gt_id_gt in Hgt. lia.
Qed.
