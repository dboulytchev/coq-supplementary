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
  (* prove_with lt_eq_lt_dec. *)
  intros [n1] [n2].
  destruct (lt_eq_lt_dec n1 n2).
  { destruct s.
    { left. left. apply lt_conv. auto. } 
    { left. right. inversion e. auto. }  
  }
  { right. apply lt_conv. auto. }
Qed.

Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 i> id2} + {id1 = id2} + {id2 i> id1}.
Proof.
  (* prove_with gt_eq_gt_dec. *)
  intros [n1] [n2].
  destruct (gt_eq_gt_dec n1 n2).
  { destruct s.
    { right. apply gt_conv. auto. } 
    { left. right. inversion e. auto. }  
  }
  { left. left. apply gt_conv. auto. }
Qed.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 i<= id2} + {id1 i> id2}.
Proof.
  (* prove_with le_gt_dec. *)
  intros [n1] [n2].
  destruct (le_gt_dec n1 n2).
  { left. apply le_conv. auto. }
  { right. apply gt_conv. auto. } 
Qed.

Lemma id_eq_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  (* prove_with Nat.eq_dec. *)
  intros [n1] [n2].
  destruct (Nat.eq_dec n1 n2).
  { left. inversion e. auto. }
  { right. injection. auto. }
Qed.

Lemma eq_id : forall (T:Type) x (p q:T), (if id_eq_dec x x then p else q) = p.
Proof.
  intros T x p q.
  destruct (id_eq_dec x x).
  { auto. }
  { destruct n. auto. }
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if id_eq_dec x y then p else q) = q.
Proof.
  intros T x y p q H.
  destruct (id_eq_dec x y).
  { destruct H. auto. }
  { auto. } 
Qed.

Lemma lt_gt_id_false : forall id1 id2 : id,
    id1 i> id2 -> id2 i> id1 -> False.
Proof.
  intros [n1] [n2] H1 H2.
  inversion H1.
  inversion H2.
  apply gt_asym in H3.
  auto.
Qed.

Lemma le_gt_id_false : forall id1 id2 : id,
    id2 i<= id1 -> id2 i> id1 -> False.
Proof.
  intros [n1] [n2] H1 H2.
  inversion H1.
  inversion H2.
  apply gt_not_le in H6.
  auto.
Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, 
    id1 i<= id2 -> {id1 = id2} + {id2 i> id1}.
Proof.
  intros id1 id2 H.
  specialize (gt_eq_gt_id_dec id1 id2).
  intro H1.
  destruct H1.
  { destruct s.
    { exfalso.
      apply le_gt_id_false with (id1:=id2) (id2:=id1).
      apply H. apply g.
    }
    { auto. } 
  }
  { apply Sumbool.sumbool_not. auto. }
Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id,
    id1 <> id2 -> {id1 i> id2} + {id2 i> id1}.
Proof.
  intros id1 id2 H.
  specialize (gt_eq_gt_id_dec id1 id2).
  intro H1.
  destruct H1.
  { destruct s.
    { auto. }
    { destruct H. auto. }
  }
  { auto. }
Qed.

Lemma eq_gt_id_false : forall id1 id2 : id,
    id1 = id2 -> id1 i> id2 -> False.
Proof.
  intros [n1] [n2] H1 H2.
  inversion H1.
  inversion H2.
  rewrite -> H0 in H4.
  specialize (gt_irrefl n2).
  auto.
Qed.
