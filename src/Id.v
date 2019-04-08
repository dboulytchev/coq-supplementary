(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

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
  intros [n1] [n2].
  pose proof (lt_eq_lt_dec n1 n2) as [[H1 | H2] | H3].
  - left. left. apply lt_conv. assumption.
  - left. right. rewrite -> H2. reflexivity.
  - right. apply lt_conv. assumption.
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof.
  prove_with gt_eq_gt_dec.
  (* intros [n1] [n2].
  pose proof (gt_eq_gt_dec n1 n2) as [[H1 | H2] | H3].
  - right. apply gt_conv. assumption. 
  - left. right. rewrite -> H2. reflexivity.
  - left. left. apply gt_conv. assumption. *)
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof.
  prove_with le_gt_dec.
  (* intros [n1] [n2]. 
  pose proof (le_gt_dec n1 n2) as [H1 | H2].
  - left. apply le_conv. assumption.
  - right. apply gt_conv. assumption. *)
Qed.

Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  prove_with Nat.eq_dec.
  (* intros [n1] [n2].
  pose proof (Nat.eq_dec n1 n2) as [H1 | H2].
  - left. apply f_equal. assumption.
  - right. intros Heq. inversion Heq as [Heq']. apply H2 in Heq'. assumption. *)
Qed.


Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof.
  intros T x p q.
  destruct (id_eq_dec x x) as [| contra].
  - reflexivity.
  - contradiction.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof.
  intros T x y p q Hneq.
  destruct (id_eq_dec x y) as [Heq | Hneq'].
  - contradiction.
  - reflexivity.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intros [n1] [n2] H1 H2.
  inversion H1.
  inversion H2.
  apply (gt_asym n1 n2).
  assumption. assumption.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof.
  intros [n1] [n2] Hle Hgt.
  inversion Hle.
  inversion Hgt.
  apply (le_not_gt n2 n1).
  assumption. assumption.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof. 
  intros [n1] [n2] Hle.
  pose proof (le_lt_eq_dec n1 n2) as [Hlt | Heq].
  - inversion Hle. assumption.
  - right. apply gt_conv. apply Hlt.
  - left. apply f_equal. assumption.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof.
  intros [n1] [n2] Hne.
  pose proof (gt_eq_gt_dec n1 n2) as [[H1 | H2] | H3].
  - right. apply gt_conv. assumption.
  - apply f_equal with (B:=id) (f:=Id) in H2.
    apply Hne in H2. contradiction.
  - left. apply gt_conv. assumption.
Qed.

Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof.
  intros [n1] [n2] HeqId HgtId.
  inversion HeqId as [Heq].
  inversion HgtId as [n1e n2e Hgt Heq1 Heq2].
  rewrite <- Heq in Hgt.
  pose proof (gt_irrefl n1) as H.
  contradiction.
Qed.