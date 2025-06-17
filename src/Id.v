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
Proof. 
  intros id1 id2.
  destruct id1 as [n1].
  destruct id2 as [n2].
  destruct (Nat.eq_dec n1 n2) as [Heq | Hneq].
  - left. rewrite Heq. reflexivity.
  - right. intro Heq. injection Heq. contradiction.
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof.
  intros T x p q.
  destruct (id_eq_dec x x) as [Heq | Hneq].
  - reflexivity.
  - contradiction Hneq. reflexivity.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof.
  intros T x y p q Hneq_xy.
  destruct (id_eq_dec x y) as [Heq | Hneq].
  - contradiction (Hneq_xy Heq).
  - reflexivity.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intros id1 id2 Hgt1 Hgt2.
  destruct id1 as [n1].
  destruct id2 as [n2].
  inversion Hgt1 as [n1' n2' Hgt_nat1 Heq1 Heq2].
  inversion Hgt2 as [n2'' n1'' Hgt_nat2 Heq3 Heq4].
  subst.
  lia.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof.
  intros id1 id2 Hle Hgt.
  destruct id1 as [n1].
  destruct id2 as [n2].
  inversion Hle as [n2' n1' Hle_nat Heq1 Heq2].
  inversion Hgt as [n2'' n1'' Hgt_nat Heq3 Heq4].
  subst.
  lia.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof.
  intros id1 id2 Hle.
  destruct id1 as [n1].
  destruct id2 as [n2].
  assert (n1 <= n2) as Hle_nat.
  { inversion_clear Hle. assumption. }
  destruct (Nat.eq_dec n1 n2) as [Heq | Hneq].
  - left. rewrite Heq. reflexivity.
  - right. constructor. lia.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof.
  intros id1 id2 Hneq.
  destruct id1 as [n1].
  destruct id2 as [n2].
  assert (n1 <> n2) as Hneq_nat.
  { intro Heq. apply Hneq. rewrite Heq. reflexivity. }
  destruct (lt_dec n1 n2) as [Hlt | Hge].
  - right. constructor. assumption.
  - left. constructor. lia.
Qed.
    
Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof.
  intros id1 id2 Heq Hgt.
  rewrite Heq in Hgt.
  destruct id2 as [n2].
  inversion Hgt as [n2' n2'' Hgt_nat Heq1 Heq2].
  subst.
  lia.
Qed.
