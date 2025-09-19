(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Lia.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.

  Variable A : Set.
  
  Definition state := list (id * A).
  
  Check [1 ; 2] : list (nat).
(* example of x * y meaning *)
Definition ex1 : list (id * nat) := [(Id 0, 1); (Id 1, 2)].
Definition ex2 : list (nat * nat) := [(1, 4)].
Definition ex3 : (nat * nat) := (1, 2). 



  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).
  
  (* Functional version of binding-in-a-state relation *)
  Fixpoint st_eval (st : state) (x : id) : option A :=
    match st with
    | (x', a) :: st' =>
        if id_eq_dec x' x then Some a else st_eval st' x
    | [] => None
    end.
 
  (* State a prove a lemma which claims that st_eval and
     st_binds are actually define the same relation.
  *)

  Lemma state_deterministic' (st : state) (x : id) (n m : option A)
    (SN : st_eval st x = n)
    (SM : st_eval st x = m) :
    n = m.
  Proof using Type.
    subst n. subst m. reflexivity.
  Qed.
  
  Lemma state_eqty (st : state) (x : id) (n : A) :
  (st_eval st x = (Some n)) <-> (st / x => n).
  Proof. split.
  - induction st as [| st' st'' ip].
    + simpl. discriminate.
  + intros e1. destruct e1. Abort.    


  Lemma stay_tuden (k x: _) (v n: _) (tael: _) 
  (SN : ((k, v) :: tael) / x => n) (e : k <> x)
   : (tael) / x => (n).
  Proof.
    inversion SN.
    - subst. contradiction e. reflexivity.
    - subst. apply H5.
  Qed.   



  (* Lemma idnes (k: id) : id_eq_dec k k = left eq_refl.
  Proof. *)
(* Qed. *)


 Lemma howwy {k : id} {v3 v : A} {tael : state} (e : st_binds ((k, v3) :: tael) k v)
 : v3 = v.
 Proof.
  inversion e.
  - reflexivity.
  - subst. contradiction.
 Qed.  

 Lemma st_eval_step {tael} {k2 k} {v3} (e : k2 <> k) : 
 st_eval ((k2, v3) :: tael) k = st_eval tael k.
 Proof.
  unfold st_eval at 1. 
  rewrite (neq_id _ _ _ _ _ e).
  fold st_eval.
  reflexivity.
 Qed.

Lemma horny {tael : state} {k2 k : id} {v v3: A} (n : k2 <> k) (e4 : st_binds ((k2, v3) :: tael) k v) :
 st_binds tael k v.
 Proof.
  inversion e4.
  - subst. contradiction.
  - subst. assumption.
 Qed.  

Lemma horny3 {tael : state} {k2 k : id} {v v3: A} (n : k2 <> k) : (st_binds ((k2, v3) :: tael) k v) 
 <-> (st_binds tael k v).
 Proof.
  split.
  + intro e4. inversion e4.
  - subst. contradiction.
  - subst. assumption.
  + intro e4.
  apply st_binds_tl.
  apply not_eq_sym in n.
  assumption. assumption.   
 Qed.  


  Lemma st_eqiv {st} {k} {v} : st / k => v <-> st_eval st k = (Some v).
  Proof.
  split.
  -
  induction st as [ | (k2, v3) tael ip].
  + intros e4. inversion e4.
  + intros e4.
   (* unfold st_eval. *)
    destruct (id_eq_dec k2 k).
    * subst k2. unfold st_eval. rewrite eq_id.
    apply howwy in e4.
    f_equal. assumption.
    *
    rewrite (st_eval_step n).
    apply (horny n) in e4.
    apply ip.
    assumption.
  
  - 
  induction st as [ | (k2, v3) tael ip].
  +  intros e4. inversion e4.
  + intros e4.
    destruct (id_eq_dec k2 k).
    * subst k2. 
    unfold st_eval in e4.
    rewrite eq_id in e4.
    injection e4 as e4.
    subst v3.
    apply st_binds_hd.
    * rewrite (st_eval_step n) in e4.
    apply (horny3 n).
    (* auto. *)
    apply ip.
    assumption.
  Qed.    

  Lemma state_deterministic (st : state) (x : id) (n m : A)   
    (SN : st / x => n)
    (SM : st / x => m) :
    n = m. 
  Proof.
    rewrite st_eqiv in SN.
    rewrite st_eqiv in SM.
    rewrite SN in SM.
    injection SM as ee.
    apply ee.
  Qed.

  

  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof.
    unfold update.
    apply st_binds_hd.
  Qed.
  
  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    unfold update.
    symmetry. 
    apply (horny3 NEQ).
  Qed.

  From Coq Require Import Setoids.Setoid.

Ltac find_head_reduction :=
  match goal with
    | H: st_eval (cons (pair ?x _) ?tail) ?x = _ |- _ =>
        unfold st_eval in H;
        rewrite eq_id in H;
        try (injection H as ?;
        subst)

    | |- st_eval (cons (pair ?x _) ?tail) ?x = _ =>
      unfold st_eval;
      rewrite eq_id;
        try (injection;
        subst)

    | H: st_eval (cons (pair ?x1 _) ?tail) ?x2 = _,
      H2: ?x1 <> ?x2 
            |- _ =>
        try (
          unfold st_eval in H;
          rewrite (neq_id _ _ _ _ _ H2) in H;
          fold st_eval in H;
          fold st_eval in H;
          try (injection H as ?;
          subst)
        )

      | H2: ?x1 <> ?x2 
            |- st_eval (cons (pair ?x1 _) ?tail) ?x2 = _ =>
        try (
          unfold st_eval;
          rewrite (neq_id _ _ _ _ _ H2);
          fold st_eval;
          try (injection;
          subst)
        )
  end.

Ltac rewrite_neq_st_eval :=
  repeat match goal with
  | H1: context[if id_eq_dec ?x ?y then _ else _] |- _ =>
      match goal with
      | H2: ?x <> ?y |- _ =>
          rewrite (neq_id _ x y _ _ H2) in H1;
          simpl in H1

      | _ => fail
      end
  | |- context[if id_eq_dec ?x ?y then _ else _] =>
      match goal with
      | H2: ?x <> ?y |- _ => 
          rewrite (neq_id _ x y _ _ H2);
          simpl
      end
  end.

Ltac rewrite_eq_st_eval :=
  repeat match goal with
  | H1: context[if id_eq_dec ?x ?y then _ else _] |- _ =>
      subst;
      try (rewrite eq_id in H1)

  | |- context[if id_eq_dec ?x ?y then _ else _] =>
      subst;
      try (rewrite eq_id)
  end.


  Lemma test : forall x1 m1 m2 st , (st_eval ((x1, m1) :: st) x1 = Some m2) -> m1 = m2.
  Proof.
    intros x1 m1 m st e.
    find_head_reduction.
    reflexivity.
  Qed.


  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof. 
  unfold update.
  destruct (id_eq_dec x2 x1);
  subst;
  rewrite st_eqiv;
  rewrite st_eqiv;
  split;
  intros e1;
  find_head_reduction;
  find_head_reduction;
  try reflexivity;
  rewrite_neq_st_eval;
  assumption.

  Qed.
Search ( _ <> _ -> _ <> _).
(* not_eq_sym *)
Ltac flip_when_see :=
  match goal with
  | H2: ?y <> ?x |- _ =>
    match goal with
    | H: context[if id_eq_dec ?x ?y then _ else _] |- _ => 
    apply not_eq_sym in H2
    
    | |- context[if id_eq_dec ?x ?y then _ else _] =>
    apply not_eq_sym in H2

    | H: context[st_eval (cons (pair ?x _) ?tail) ?y]|- _ =>
    apply not_eq_sym in H2

    | |- context[st_eval (cons (pair ?x _) ?tail) ?y] =>
    apply not_eq_sym in H2

    end
  end.
  
Ltac redu := 
  subst;
  try flip_when_see;
  try find_head_reduction;
  try rewrite_neq_st_eval;
  try rewrite_eq_st_eval;
  fold st_eval.

  


  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
  rewrite st_eqiv.
  unfold update.
  destruct (id_eq_dec x1 x2);
  redu;
  rewrite st_eqiv in SN;
  rewrite st_eqiv in SM;
  redu.
  - congruence.
  - assumption.
  Qed.
  
  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    unfold update.
    unfold update in SM.
    rewrite st_eqiv in SM.
    rewrite st_eqiv.
    rewrite <- SM.
    destruct (id_eq_dec x3 x1);
    destruct (id_eq_dec x3 x2);
    redu;
    redu;
    try(destruct (id_eq_dec x1 x2);
    redu;
    redu);
    try (contradiction);
    try (reflexivity).
  Qed.

  Lemma state_extensional_equivalence (st st' : state) (H: forall x z, st / x => z <-> st' / x => z) : st = st'.
  Proof. 
(* это не всегда правда! у нас старые ключи из стека не удаляются, и для интерфейса get они не видны но внутри объекта хранятся делая его другимs *)
(* при этом без дополнительной информации о том, обитаем ли A, нельзя доказать ни state_extensional_equivalence, ни ~ state_extensional_equivalence *)
(* оба утверждения верны или не верны в зависимости от того, обитаемо ли множество A *)
admit. Admitted.



  Definition state_equivalence (st st' : state) := forall x a, st / x => a <-> st' / x => a.

  Notation "st1 ~~ st2" := (state_equivalence st1 st2) (at level 0).

  Lemma st_equiv_refl (st: state) : st ~~ st.
  Proof.
  split;
  intro e;
  apply e.
Qed.

  Lemma st_equiv_symm (st st': state) (H: st ~~ st') : st' ~~ st.
  Proof.
  split;
  apply H.
  Qed. 

  Lemma st_equiv_trans (st st' st'': state) (H1: st ~~ st') (H2: st' ~~ st'') : st ~~ st''.
  Proof.
  split;
  intro e.
  - 
  apply H2.
  apply H1.
  assumption.
  - 
  apply H1.
  apply H2.
  assumption.
  Qed.

  Lemma equal_states_equive (st st' : state) (HE: st = st') : st ~~ st'.
  Proof.
  split;
  intro e;
  subst; assumption.
  Qed.
  
End S.

Ltac flip_when_see :=
  match goal with
  | H2: ?y <> ?x |- _ =>
    match goal with
    | H: context[if id_eq_dec ?x ?y then _ else _] |- _ => 
    apply not_eq_sym in H2
    
    | |- context[if id_eq_dec ?x ?y then _ else _] =>
    apply not_eq_sym in H2

    | H: context[st_eval (cons (pair ?x _) ?tail) ?y]|- _ =>
    apply not_eq_sym in H2

    | |- context[st_eval (cons (pair ?x _) ?tail) ?y] =>
    apply not_eq_sym in H2

    end
  end.

Ltac find_head_reduction :=
  match goal with
    | H: st_eval (cons (pair ?x _) ?tail) ?x = _ |- _ =>
        unfold st_eval in H;
        rewrite eq_id in H;
        try (injection H as ?;
        subst)

    | |- st_eval (cons (pair ?x _) ?tail) ?x = _ =>
      unfold st_eval;
      rewrite eq_id;
        try (injection;
        subst)

    | H: st_eval (cons (pair ?x1 _) ?tail) ?x2 = _,
      H2: ?x1 <> ?x2 
            |- _ =>
        try (
          unfold st_eval in H;
          rewrite (neq_id _ _ _ _ _ H2) in H;
          fold st_eval in H;
          fold st_eval in H;
          try (injection H as ?;
          subst)
        )

      | H2: ?x1 <> ?x2 
            |- st_eval (cons (pair ?x1 _) ?tail) ?x2 = _ =>
        try (
          unfold st_eval;
          rewrite (neq_id _ _ _ _ _ H2);
          fold st_eval;
          try (injection;
          subst)
        )
  end.
Ltac rewrite_neq_st_eval :=
  repeat match goal with
  | H1: context[if id_eq_dec ?x ?y then _ else _] |- _ =>
      match goal with
      | H2: ?x <> ?y |- _ =>
          rewrite (neq_id _ x y _ _ H2) in H1;
          simpl in H1

      | _ => fail
      end
  | |- context[if id_eq_dec ?x ?y then _ else _] =>
      match goal with
      | H2: ?x <> ?y |- _ => 
          rewrite (neq_id _ x y _ _ H2);
          simpl
      end
  end.

Ltac rewrite_eq_st_eval :=
  repeat match goal with
  | H1: context[if id_eq_dec ?x ?y then _ else _] |- _ =>
      subst;
      try (rewrite eq_id in H1)

  | |- context[if id_eq_dec ?x ?y then _ else _] =>
      subst;
      try (rewrite eq_id)
  end.
Ltac redu := 
  subst;
  try flip_when_see;
  try find_head_reduction;
  try rewrite_neq_st_eval;
  try rewrite_eq_st_eval;
  fold st_eval.