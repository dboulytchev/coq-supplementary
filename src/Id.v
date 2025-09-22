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
  intros. destruct id_eq_dec as [_|D].
  - reflexivity.
  - unfold not in D. destruct D. reflexivity.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof. 
  intros. destruct id_eq_dec as [D|_].
  -  unfold not in H. apply H in D. destruct D.
  - reflexivity.
Qed.

Lemma lt_gt_false: forall n m : nat,
  n > m -> m > n -> False.
Proof.
  intros.
  unfold gt in H.
  unfold gt in H0.
  set (Nat.lt_trans n m n) as J.
  apply J in H0.
  - set (Nat.lt_irrefl n) as J2. unfold not in J2. apply J2 in H0. destruct H0.
  - apply H. 
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof. 
  intros.
  inversion H.
  inversion H0.
  rewrite <- H3 in H5. injection H5 as H5.
  rewrite <- H2 in H6. injection H6 as H6.
  rewrite H5 in H4. rewrite H6 in H4.
  apply lt_gt_false in H1.
  - destruct H1.
  - apply H4.
Qed.


Lemma le_gt_false: forall n m : nat,
  m <= n -> m > n -> False.
Proof.
  intros.
  unfold gt in H0.
  set (Nat.lt_le_trans n m n) as J.
  apply J in H0.
  - set (Nat.lt_irrefl n) as J2. unfold not in J2. apply J2 in H0. destruct H0.
  - apply H. 
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof. 
  intros.
  inversion H.
  inversion H0.
  rewrite <- H3 in H6. injection H6 as H6.
  rewrite <- H2 in H5. injection H5 as H5.
  rewrite H5 in H4. rewrite H6 in H4.
  apply le_gt_false in H1.
  - destruct H1.
  - apply H4.
Qed.


Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof. 
  intros.
  destruct id1, id2.
  destruct (n ?= n0) eqn:res.
  - apply Nat.compare_eq in res. left. apply f_equal. apply res.
  - apply Nat.compare_lt_iff in res. right.  
    assert (J: n0 > n). { apply res. } apply gt_conv in J. apply J.
  - apply Nat.compare_gt_iff in res. assert (J: n > n0). { apply res. }
    apply gt_conv in J. apply le_gt_id_false in H.
    * destruct H.
    * apply J.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof.
  intros.
  destruct id1, id2.
  destruct (n ?= n0) eqn:res.
  - apply Nat.compare_eq in res. unfold not in H. destruct H. apply f_equal. apply res.
  - apply Nat.compare_lt_iff in res. right.  
  assert (J: n0 > n). { apply res. } apply gt_conv in J. apply J.
  - apply Nat.compare_gt_iff in res. assert (J: n > n0). { apply res. }
  apply gt_conv in J. left. apply J.
Qed.

Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof. intros.
  destruct H.
  inversion H0.
  unfold gt in H2.
  specialize Nat.lt_irrefl with n. unfold not.
  intros. apply H3 in H2. destruct H2.
Qed.
