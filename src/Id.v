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
  intros.
  destruct id1 as [n1]. destruct id2 as [n2].
  remember lt_eq_lt_dec as s.
  pose proof (s n1 n2) as H.
  destruct H as [H2' | H3]. destruct H2' as [H1 | H2].
  - left. left. apply lt_conv. auto.
  - left. right. auto.
  - right. apply lt_conv. auto.
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof. 
  intros.
  destruct id1 as [n1]. destruct id2 as [n2].
  remember gt_eq_gt_dec as s.
  pose proof (s n1 n2) as H.
  destruct H as [H2' | H3]. destruct H2' as [H1 | H2].
  - right. apply gt_conv. auto.
  - left. right. auto.
  - left. left. apply gt_conv. auto.
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof. 
  intros.
  destruct id1 as [n1]. destruct id2 as [n2].
  remember le_gt_dec as s.
  pose proof (s n1 n2) as H.
  destruct H as [H1 | H2].
  - left. apply le_conv. auto.
  - right. apply gt_conv. auto.
Qed.

Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. 
  intros.
  destruct id1 as [n1]. destruct id2 as [n2].
  remember eq_nat_dec as s.
  pose proof (s n1 n2) as H.
  destruct H as [H1 | H2].
  left. auto.
  right. intro M. 
  assert (n1 = n2) as M2. { inversion M. auto. }
  auto.
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof. 
  intros.
  destruct (id_eq_dec x x).
  - auto.
  - contradict n. auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof. 
  intros.
  destruct (id_eq_dec x y) as [H1 | H2].
  - contradict H1. auto.
  - auto.
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intros id1 id2.
  intros H1 H2.
  destruct id1 as [n1]. destruct id2 as [n2].
  assert (n1 > n2) as HR. { inversion H1. auto. }
  assert (n1 < n2) as HL. { inversion H2. auto. }
  intuition.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof. 
  intros id1 id2.
  intros H1 H2.
  destruct id1 as [n1]. destruct id2 as [n2].
  assert (n2 <= n1) as HR. { inversion H1. auto. }
  assert (n2 > n1) as HL. { inversion H2. auto. }
  intuition.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof. 
  intros id1 id2.
  intro H.
  destruct id1 as [n1]. destruct id2 as [n2].
  remember le_lt_eq_dec as s.
  pose proof (s n1 n2) as P.
  assert (n1 <= n2) as LE. { inversion H. auto. }
  pose proof (P LE) as PS.
  destruct PS as [PS1 | PS2].
  - right. 
    assert (n2 > n1). { auto. }
    apply gt_conv. auto.
  - left. auto.
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof.
  intros id1 id2.
  intro H.
  remember gt_eq_gt_id_dec as P.
  pose proof (P id1 id2) as PS.
  destruct PS as [P2' | P3].
  destruct P2' as [P1 | P2].
  - left. apply P1.
  - contradict H. apply P2.
  - right. apply P3.
Qed.

Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof. 
  intros id1 id2.
  destruct id1 as [n1]. destruct id2 as [n2].
  intro E. intro G.
  assert (n1 = n2) as EN. { inversion E. auto. }
  assert (n1 > n2) as GN. { inversion G. auto. }
  intuition.
Qed.
