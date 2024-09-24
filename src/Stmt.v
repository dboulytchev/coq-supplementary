Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Coq.Program.Equality.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

From hahn Require Import HahnBase.

(* AST for statements *)
Inductive stmt : Type :=
| SKIP  : stmt
| Assn  : id -> expr -> stmt
| READ  : id -> stmt
| WRITE : expr -> stmt
| Seq   : stmt -> stmt -> stmt
| If    : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf := (state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "c1 '==' s '==>' c2" (at level 0).

Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop :=
| bs_Skip        : forall (c : conf), c == SKIP ==> c
| bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
                          (s, i, o) == x ::= e ==> (s [x <- z], i, o)
| bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                          (s, z::i, o) == READ x ==> (s [x <- z], i, o)
| bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
                          (s, i, o) == WRITE e ==> (s, i, z::o)
| bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt)
                          (STEP1 : c == s1 ==> c') (STEP2 : c' == s2 ==> c''),
                          c ==  s1 ;; s2 ==> c''
| bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                          (CVAL : [| e |] s => Z.one)
                          (STEP : (s, i, o) == s1 ==> c'),
                          (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                          (CVAL : [| e |] s => Z.zero)
                          (STEP : (s, i, o) == s2 ==> c'),
                          (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt)
                          (CVAL  : [| e |] st => Z.one)
                          (STEP  : (st, i, o) == s ==> c')
                          (WSTEP : c' == WHILE e DO s END ==> c''),
                          (st, i, o) == WHILE e DO s END ==> c''
| bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt)
                          (CVAL : [| e |] st => Z.zero),
                          (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

#[export] Hint Constructors bs_int : core.

(* "Surface" semantics *)
Definition eval (s : stmt) (i o : list Z) : Prop :=
  exists st, ([], i, []) == s ==> (st, [], o).

Notation "<| s |> i => o" := (eval s i o) (at level 0).

(* "Surface" equivalence *)
Definition eval_equivalent (s1 s2 : stmt) : Prop :=
  forall (i o : list Z),  <| s1 |> i => o <-> <| s2 |> i => o.

Notation "s1 ~e~ s2" := (eval_equivalent s1 s2) (at level 0).

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt :=
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s)
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Definition contextual_equivalent (s1 s2 : stmt) :=
  forall (C : Context), (C <~ s1) ~e~ (C <~ s2).

Notation "s1 '~c~' s2" := (contextual_equivalent s1 s2) (at level 42, no associativity).

Lemma contextual_equiv_stronger (s1 s2 : stmt) (H: s1 ~c~ s2) : s1 ~e~ s2.
Proof.
  unfold contextual_equivalent in H.
  specialize (H Hole).
  simpl in H.
  assumption.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists ((Id 0) ::= (Nat 0)), ((Id 1) ::= (Nat 1)).
  split.
  {
    unfold eval_equivalent.
    intros.
    split;
    intros;
    inversion H;
    inversion H0;
    repeat econstructor.
  }
  {
    intro.
    unfold contextual_equivalent in H.
    specialize (H (SeqL (Hole) (WRITE (Var (Id 0))))).
    unfold eval_equivalent in H.
    specialize (H ([]) ([Z.zero])).
    inversion H.
    assert (<| SeqL Hole (WRITE (Var (Id 0))) <~ Id 1 ::= Nat 1 |> [] => ([Z.zero]) -> False).
    {
      intro.
      inversion H2.
      inversion H3.
      inversion STEP1.
      inversion VAL.
      subst.
      inversion STEP2.
      subst.
      inversion VAL0.
      subst.
      inversion VAR.
      inversion H10.
    }
    assert (<| SeqL Hole (WRITE (Var (Id 0))) <~ Id 0 ::= Nat 0 |> [] => ([Z.zero])).
    {
      simpl.
      repeat econstructor.
    }
    apply H2.
    apply H0.
    assumption.
  }
Qed.


(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Ltac seq_inversion :=
  match goal with
    H: _ == _ ;; _ ==> _ |- _ => inversion_clear H
  end.

Ltac seq_apply :=
  match goal with
  | H: _   == ?s1 ==> ?c' |- _ == (?s1 ;; _) ==> _ =>
    apply bs_Seq with c'; solve [seq_apply | assumption]
  | H: ?c' == ?s2 ==>  _  |- _ == (_ ;; ?s2) ==> _ =>
    apply bs_Seq with c'; solve [seq_apply | assumption]
  end.

Module SmokeTest.

  (* Associativity of sequential composition *)
  Lemma seq_assoc (s1 s2 s3 : stmt) :
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
    unfold bs_equivalent.
    intros.
    split;
    intro;
    seq_inversion;
    seq_inversion;
    seq_apply.
  Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros c c'.
    split.
    - intros H.
      inversion H; subst.
      + apply bs_If_True.
        * assumption.
        * apply bs_Seq with c'0; assumption.
      + apply bs_If_False.
        * assumption.
        * apply bs_Skip.
    - intros H. inversion H; subst.
      + inversion STEP; subst.
        apply bs_While_True with c'0; assumption.
      + inversion STEP; subst.
        apply bs_While_False.
        assumption.
  Qed.
End SmokeTest.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent.
  split;
  intros;
  inversion H;
  subst.
  2, 4:
    constructor 7;
    assumption.

  {
    econstructor.
    { assumption. }
    { apply EQ. assumption. }
  }
  {
    econstructor.
    { assumption. }
    { apply EQ. assumption. }
  }
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  unfold bs_equivalent.
  split;
  intros;
  dependent induction H;
  eauto.
  {
    econstructor.
    assumption.
    apply EQ.
    eassumption.
    eauto.
  }
  {
    econstructor.
    assumption.
    apply EQ.
    eassumption.
    eauto.
  }
Qed.

Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent.
  intros c c'.
  split; intros H;
    inversion H; subst;
    apply bs_Seq with c'0;
    [ assumption | apply EQ; assumption
      | assumption | apply EQ; assumption ].
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent.
  intros c c'.
  split; intros; inversion H; subst; apply bs_Seq with c'0; try assumption; try apply EQ; assumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent.
  intros c c'.
  split; intros H; inversion H; subst.
  1, 3: apply bs_If_True; try assumption.
  all: apply bs_If_False; try assumption; apply EQ; assumption.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split.
  apply eq_congruence_seq_r. assumption.
  split.
  apply eq_congruence_seq_l. assumption.
  split.
  apply eq_congruence_cond_else. assumption.
  split.
  apply eq_congruence_cond_then. assumption.
  apply eq_congruence_while. assumption.
Qed.

(* Big-step semantics is deterministic *)
Ltac by_eval_deterministic :=
  match goal with
    H1: [|?e|]?s => ?z1, H2: [|?e|]?s => ?z2 |- _ =>
     apply (eval_deterministic e s z1 z2) in H1; [subst z2; reflexivity | assumption]
  end.

Ltac eval_zero_not_one :=
  match goal with
    H : [|?e|] ?st => (Z.one), H' : [|?e|] ?st => (Z.zero) |- _ =>
    assert (Z.zero = Z.one) as JJ; [ | inversion JJ];
    eapply eval_deterministic; eauto
  end.

Lemma bs_int_deterministic (c c1 c2 : conf) (s : stmt)
      (EXEC1 : c == s ==> c1) (EXEC2 : c == s ==> c2) :
  c1 = c2.
Proof.
  generalize dependent c1.
  induction EXEC2;
  intros.
  {
    inversion EXEC1.
    reflexivity.
  }
  {
    inversion EXEC1.
    subst.
    specialize (eval_deterministic _ _ _ _ VAL VAL0) as Hz_eq_z0.
    subst.
    reflexivity.
  }
  {
    inversion EXEC1.
    subst.
    reflexivity.
  }
  {
    inversion EXEC1.
    subst.
    specialize (eval_deterministic _ _ _ _ VAL VAL0) as Hz_eq_z0.
    subst.
    reflexivity.
  }
  {
    inversion EXEC1.
    subst.
    specialize (IHEXEC2_1 c'0 STEP1).
    subst.
    specialize (IHEXEC2_2 c1 STEP2).
    subst.
    reflexivity.
  }
  {
    inversion EXEC1;
    subst.
    {
      specialize (IHEXEC2 c1 STEP).
      subst.
      reflexivity.
    }
    {
      specialize (eval_deterministic _ _ _ _ CVAL CVAL0) as Hzero_eq_one.
      inversion Hzero_eq_one.
    }
  }
  {
    inversion EXEC1;
    subst.
    {
      specialize (eval_deterministic _ _ _ _ CVAL CVAL0) as Hzero_eq_one.
      inversion Hzero_eq_one.
    }
    {
      specialize (IHEXEC2 c1 STEP).
      subst.
      reflexivity.
    }
  }
  {
    inversion EXEC1;
    subst.
    {
      specialize (IHEXEC2_1 c'0 STEP).
      subst.
      specialize (IHEXEC2_2 c1 WSTEP).
      subst.
      reflexivity.
    }
    {
      specialize (eval_deterministic _ _ _ _ CVAL CVAL0) as Hzero_eq_one.
      inversion Hzero_eq_one.
    }
  }
  {
    inversion EXEC1;
    subst.
    {
      specialize (eval_deterministic _ _ _ _ CVAL CVAL0) as Hzero_eq_one.
      inversion Hzero_eq_one.
    }
    {
      reflexivity.
    }
  }
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma equiv_states_equiv_update (s1 s2 : state Z)
                                (HE : equivalent_states s1 s2)
                                (i : id) (z : Z) :
  equivalent_states (s1 [i <- z]) (s2 [i <- z]).
Proof.
  unfold equivalent_states.
  intros.
  unfold Expr.equivalent_states.
  split;
  intros.
  {
    inversion H;
    subst.
    {
      constructor.
    }
    {
      constructor.
      { assumption. }
      { apply HE. assumption. }
    }
  }
  {
    inversion H;
    subst.
    { constructor. }
    {
      constructor.
      { assumption. }
      { apply HE. assumption. }
    }
  }
Qed.

Lemma equiv_states_equiv_eval (s1 s2 : state Z)
                              (HE : equivalent_states s1 s2)
                              (e : expr) (z : Z)
                              (H : [|e|] s1 => z) :
  [|e|] s2 => z.
Proof.
  induction H;
  eauto.
  {
    constructor.
    apply HE.
    assumption.
  }
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  remember (st1, i, o).
  remember (st2, i', o').
  generalize i o i' o' st1 st2 st1' HE1 Heqp Heqp0.
  clear Heqp Heqp0 HE1 o i' o' i HE1 st1 st2 st1'.
  induction H;
  intros.
  {
    rewrite Heqp in Heqp0.
    inversion Heqp0.
    exists st1'.
    subst.
    split;
    auto.
  }

  {
    inversion Heqp;
    inversion Heqp0;
    subst.
    exists (st1' [x <- z]).
    split.
    {
      apply equiv_states_equiv_update.
      assumption.
    }
    {
      constructor.
      eapply equiv_states_equiv_eval;
      eauto.
    }
  }
  {
    inversion Heqp;
    inversion Heqp0;
    subst.
    exists (st1' [x <- z]).
    split.
    {
      apply equiv_states_equiv_update.
      assumption.
    }
    {
      constructor.
    }
  }
  {
    inversion Heqp;
    inversion Heqp0;
    subst.
    exists (st1').
    split.
    { assumption. }
    {
      constructor.
      eapply equiv_states_equiv_eval;
      eauto.
    }
  }
  {
    inversion Heqp;
    inversion Heqp0;
    subst.
    destruct c'.
    destruct p.
    specialize (IHbs_int1 i o l0 l st1 s st1' HE1 H1).
    assert ((s, l0, l) = (s, l0, l)).
      reflexivity.
    specialize (IHbs_int1 H3).
    inversion_clear IHbs_int1.
    inversion_clear H4.
    specialize (IHbs_int2 l0 l i' o' s st2 x H5 H3 H2).
    inversion_clear IHbs_int2.
    inversion_clear H4.
    eauto.
  }
  {
    inversion Heqp;
    inversion Heqp0;
    subst.
    specialize (IHbs_int i0 o0 i' o' st1 st2 st1' HE1 Heqp H0).
    inversion_clear IHbs_int.
    inversion_clear H1.
    exists x.
    split.
    { assumption. }
    {
      constructor.
      eapply equiv_states_equiv_eval;
      eassumption.
      auto.
    }
  }
  {
    inversion Heqp;
    inversion Heqp0;
    subst.
    specialize (IHbs_int i0 o0 i' o' st1 st2 st1' HE1 Heqp H0).
    inversion_clear IHbs_int.
    inversion_clear H1.
    exists x.
    split.
    { assumption. }
    {
      constructor 7.
      eapply equiv_states_equiv_eval;
      eassumption.
      auto.
    }
  }
  {
    inversion Heqp;
    inversion Heqp0;
    subst.
    destruct c', p.
    specialize (IHbs_int1 i0 o0 l0 l st1 s0 st1' HE1 Heqp).
    assert ((s0, l0, l) = (s0, l0, l)). reflexivity.
    specialize (IHbs_int1 H2).
    inversion_clear IHbs_int1.
    inversion_clear H3.

    specialize (IHbs_int2 l0 l i' o' s0 st2 x H4 H2 H1).
    inversion_clear IHbs_int2.
    inversion_clear H3.

    exists x0;
    split.
    { assumption. }
    {
      econstructor.
      { eapply equiv_states_equiv_eval; eassumption. }
      { eassumption. }
      { assumption. }
    }
  }
  {
    inversion Heqp;
    inversion Heqp0;
    subst.
    exists st1'.
    split.
    { assumption. }
    {
      constructor.
      eapply equiv_states_equiv_eval;
      eassumption.
    }
  }
Qed.

(* Contextual equivalence is equivalent to the semantic one *)
(* TODO: no longer needed *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); assumption.

(* Small-step semantics *)
Module SmallStep.

  Reserved Notation "c1 '--' s '-->' c2" (at level 0).

  Inductive ss_int_step : stmt -> conf -> option stmt * conf -> Prop :=
  | ss_Skip        : forall (c : conf), c -- SKIP --> (None, c)
  | ss_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                            (SVAL : [| e |] s => z),
      (s, i, o) -- x ::= e --> (None, (s [x <- z], i, o))
  | ss_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
      (s, z::i, o) -- READ x --> (None, (s [x <- z], i, o))
  | ss_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                            (SVAL : [| e |] s => z),
      (s, i, o) -- WRITE e --> (None, (s, i, z::o))
  | ss_Seq_Compl   : forall (c c' : conf) (s1 s2 : stmt)
                            (SSTEP : c -- s1 --> (None, c')),
      c -- s1 ;; s2 --> (Some s2, c')
  | ss_Seq_InCompl : forall (c c' : conf) (s1 s2 s1' : stmt)
                            (SSTEP : c -- s1 --> (Some s1', c')),
      c -- s1 ;; s2 --> (Some (s1' ;; s2), c')
  | ss_If_True     : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.one),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s1, (s, i, o))
  | ss_If_False    : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.zero),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s2, (s, i, o))
  | ss_While       : forall (c : conf) (s : stmt) (e : expr),
      c -- WHILE e DO s END --> (Some (COND e THEN s ;; WHILE e DO s END ELSE SKIP END), c)
  where "c1 -- s --> c2" := (ss_int_step s c1 c2).

  Reserved Notation "c1 '--' s '-->>' c2" (at level 0).

  Inductive ss_int : stmt -> conf -> conf -> Prop :=
    ss_int_Base : forall (s : stmt) (c c' : conf),
                    c -- s --> (None, c') -> c -- s -->> c'
  | ss_int_Step : forall (s s' : stmt) (c c' c'' : conf),
                    c -- s --> (Some s', c') -> c' -- s' -->> c'' -> c -- s -->> c''
  where "c1 -- s -->> c2" := (ss_int s c1 c2).

  Lemma ss_int_step_deterministic (s : stmt)
        (c : conf) (c' c'' : option stmt * conf)
        (EXEC1 : c -- s --> c')
        (EXEC2 : c -- s --> c'') :
    c' = c''.
  Proof.
    dependent induction s;
    dependent destruction EXEC1;
    dependent destruction EXEC2;
    try reflexivity;
    try by_eval_deterministic;
    try specialize (IHs1 _ _ _ EXEC1 EXEC2);
    try inversion IHs1;
    try reflexivity;
    eval_zero_not_one.
  Qed.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    dependent induction STEP1;
    destruct STEP2;
    specialize (ss_int_step_deterministic _ _ _ _ H H0) as Hc'_eq_c'0;
    inversion Hc'_eq_c'0;
    subst;
    auto.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP;
    constructor;
    assumption.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'.
  Proof.
    generalize dependent c'.
    induction STEP1;
    intros.
    {
      econstructor 2.
      {
        constructor.
        eassumption.
      }
      {
        assumption.
      }
    }
    {
      econstructor 2.
      {
        constructor 6.
        eassumption.
      }
      {
        auto.
      }
    }
  Qed.


  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent EXEC.
    generalize dependent STEP.
    generalize c c' c''.
    dependent induction s;
    intros.
    {
      inversion STEP.
    }
    {
      inversion STEP.
    }
    {
      inversion STEP.
    }
    {
      inversion STEP.
    }
    {
      inversion STEP;
      subst.
      {
        econstructor.
        2: {
          eassumption.
        }
        apply ss_bs_base.
        assumption.
      }
      {
        inversion EXEC.
        subst.
        econstructor.
        2: {
          eassumption.
        }
        specialize (IHs1 s1' c0 c'0 c'1 SSTEP STEP1).
        assumption.
      }
    }
    {
      inversion STEP;
      subst.
      {
        constructor;
        assumption.
      }
      {
        constructor 7;
        assumption.
      }
    }
    {
      dependent induction STEP.
      inversion EXEC;
      subst;
      inversion STEP;
      subst.
      {
        econstructor;
        eassumption.
      }
      {
        econstructor 9;
        eassumption.
      }
    }
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split;
    intros.
    {
      dependent induction s.
      1-4:
        constructor.
        inversion H.
        subst.
        constructor.

      1-3:
        inversion H;
        constructor;
        assumption.

      {
        inversion H.
        subst.
        specialize (IHs1 c c'0 STEP1).
        specialize (IHs2 c'0 c' STEP2).
        apply (ss_ss_composition _ _ _ _ _ IHs1 IHs2).
      }

      {
        inversion H;
        subst;
        econstructor 2.
        {
          econstructor.
          assumption.
        }
        {
          apply (IHs1 ((s, i, o)) c' STEP).
        }
        {
          econstructor 8.
          assumption.
        }
        {
          apply (IHs2 ((s, i, o)) c' STEP).
        }
      }

      {
        dependent induction H.
        {
          econstructor 2.
          {
            econstructor.
          }
          {
            econstructor 2.
            {
              constructor.
              assumption.
            }
            {
              eapply ss_ss_composition.
              { eapply IHs. eassumption. }
              { auto. }
            }
          }
        }
        {
          econstructor 2.
          {
            constructor.
          }
          {
            econstructor 2.
            { constructor 8. assumption. }
            { repeat constructor. }
          }
        }
      }
    }
    {
      dependent induction H.
      {
        apply ss_bs_base.
        assumption.
      }
      {
        eapply ss_bs_step;
        eassumption.
      }
    }
  Qed.

End SmallStep.

Module Renaming.

  Definition renaming := Renaming.renaming.

  Definition rename_conf (r : renaming) (c : conf) : conf :=
    match c with
    | (st, i, o) => (Renaming.rename_state r st, i, o)
    end.

  Lemma re_rename_conf r c r':
    Renaming.renamings_inv r r' ->
    c = rename_conf r (rename_conf r' c).
  Proof.
    intros.
    destruct c. destruct p.
    simpl.
    rewrite Renaming.re_rename_state.
    reflexivity.
    auto.
  Qed.

  Fixpoint rename (r : renaming) (s : stmt) : stmt :=
    match s with
    | SKIP                       => SKIP
    | x ::= e                    => (Renaming.rename_id r x) ::= Renaming.rename_expr r e
    | READ x                     => READ (Renaming.rename_id r x)
    | WRITE e                    => WRITE (Renaming.rename_expr r e)
    | s1 ;; s2                   => (rename r s1) ;; (rename r s2)
    | COND e THEN s1 ELSE s2 END => COND (Renaming.rename_expr r e) THEN (rename r s1) ELSE (rename r s2) END
    | WHILE e DO s END           => WHILE (Renaming.rename_expr r e) DO (rename r s) END
    end.

  Lemma expr_rename
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (e    : expr) : Renaming.rename_expr r (Renaming.rename_expr r' e) = e.
  Proof.
    induction e.
    {
      simpl.
      reflexivity.
    }
    {
      simpl.
      specialize (Hinv i) as Hi.
      rewrite ->Hi.
      reflexivity.
    }
    {
      simpl.
      rewrite ->IHe1.
      rewrite ->IHe2.
      reflexivity.
    }
  Qed.

  Lemma re_rename
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (s    : stmt) : rename r (rename r' s) = s.
  Proof.
    unfold Renaming.renamings_inv in Hinv.
    induction s;
    simpl.
    {
      reflexivity.
    }
    {
      specialize (Hinv i) as Hi.
      rewrite ->Hi.

      specialize (expr_rename r r' Hinv e) as Hexpr.
      rewrite ->Hexpr.

      reflexivity.
    }
    {
      specialize (Hinv i).
      rewrite ->Hinv.
      reflexivity.
    }
    {
      specialize (expr_rename r r' Hinv e) as Hexpr.
      rewrite ->Hexpr.
      reflexivity.
    }
    {
      rewrite ->IHs1.
      rewrite ->IHs2.
      reflexivity.
    }
    {
      specialize (expr_rename r r' Hinv e) as Hexpr.
      rewrite ->Hexpr.
      rewrite ->IHs1.
      rewrite ->IHs2.
      reflexivity.
    }
    {
      specialize (expr_rename r r' Hinv e) as Hexpr.
      rewrite ->Hexpr.
      rewrite ->IHs.
      reflexivity.
    }
  Qed.

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    induction st;
    unfold update;
    destruct r;
    simpl;
    reflexivity.
  Qed.

  (* #[export] Hint Resolve Renaming.eval_renaming_invariance : core. *)

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    induction Hbs;
    destruct r.
    {
      constructor.
    }
    {
      constructor.
      apply Renaming.eval_renaming_invariance.
      assumption.
    }
    {
      constructor.
    }
    {
      constructor.
      apply Renaming.eval_renaming_invariance.
      assumption.
    }
    {
      econstructor;
      eassumption.
    }
    {
      constructor.
      { apply Renaming.eval_renaming_invariance. assumption. }
      { assumption. }
    }
    {
      constructor 7.
      { apply Renaming.eval_renaming_invariance. assumption. }
      { assumption. }
    }
    {
      econstructor.
      { apply Renaming.eval_renaming_invariance. assumption. }
      { eassumption. }
      { assumption. }
    }
    {
      constructor.
      apply Renaming.eval_renaming_invariance.
      assumption.
    }
  Qed.


  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r).

    remember (rename r s) as s'.
    remember (rename_conf r c) as c_.
    remember (rename_conf r c') as c'_.

    apply f_equal with (f := rename x) in Heqs'.
    rewrite re_rename in Heqs'.

    apply f_equal with (f := rename_conf x) in Heqc_, Heqc'_.
    rewrite <- (re_rename_conf) with (r := x) in Heqc_, Heqc'_.

    subst.

    apply renaming_invariant_bs. assumption.
    assumption.
    assumption.
    assumption.
  Qed.


  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof. admit. Admitted.

End Renaming.

(* CPS semantics *)
Inductive cont : Type :=
| KEmpty : cont
| KStmt  : stmt -> cont.

Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont)
                           (CSTEP : KEmpty |- c -- k --> c'),
    k |- c -- !SKIP --> c'
| cps_Assign      : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (e : expr) (n : Z)
                           (CVAL : [| e |] s => n)
                           (CSTEP : KEmpty |- (s [x <- n], i, o) -- k --> c'),
    k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (z : Z)
                           (CSTEP : KEmpty |- (s [x <- z], i, o) -- k --> c'),
    k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (z : Z)
                           (CVAL : [| e |] s => z)
                           (CSTEP : KEmpty |- (s, i, z::o) -- k --> c'),
    k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt)
                           (CSTEP : !s2 @ k |- c -- !s1 --> c'),
    k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                           (CVAL : [| e |] s => Z.one)
                           (CSTEP : k |- (s, i, o) -- !s1 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                           (CVAL : [| e |] s => Z.zero)
                           (CSTEP : k |- (s, i, o) -- !s2 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                           (CVAL : [| e |] st => Z.one)
                           (CSTEP : !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                           (CVAL : [| e |] st => Z.zero)
                           (CSTEP : KEmpty |- (st, i, o) -- k --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Lemma if_seq_comm: forall c1 c2 e s1 s2 scomm,
  c1 == COND e THEN s1 ELSE s2 END;; scomm ==> c2 <->
    c1 == COND e THEN s1;; scomm ELSE s2;;scomm END ==> c2.
Proof.
  intros c1 c2 e s1 s2 scomm.
  split; intros H.
  - inversion H; subst.
    inversion STEP1; subst.
    + apply bs_If_True.
      * assumption.
      * econstructor; eassumption.
    + apply bs_If_False.
      * assumption.
      * econstructor; eassumption.
  - inversion H; subst; inversion STEP; subst; apply bs_Seq with c'.
      * apply bs_If_True; assumption.
      * assumption.
      * apply bs_If_False; assumption.
      * assumption.
Qed.

Ltac cps_bs_gen_helper k H HH :=
  destruct k eqn:K; subst; inversion H; subst;
  [inversion EXEC; subst | eapply bs_Seq; eauto];
  apply HH; auto.

Lemma while_unfold_seq : forall c1 c2 e st sttail,
  c1 == WHILE e DO st END;; sttail ==> c2 <->
    c1 == (COND e THEN (st ;; WHILE e DO st END) ELSE SKIP END);; sttail ==> c2.
Proof.
  intros.
  split; intros H.
  - inversion H; subst.
    apply SmokeTest.while_unfolds in STEP1; apply bs_Seq with c'; assumption.
  - inversion H; subst.
    apply SmokeTest.while_unfolds in STEP1; apply bs_Seq with  c'; assumption.
Qed.

Lemma skip_left_elim: forall c1 c2 st,
  c1 == SKIP;; st ==> c2 <-> c1 == st ==> c2.
Proof.
  intros.
  split; intros H.
  - inversion H; subst. inversion STEP1. assumption.
  - apply bs_Seq with c1.
    * constructor.
    * auto.
Qed.

Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof.
  generalize dependent S.
  induction EXEC; intros S H.
  - inversion H.
  - destruct k.
    + unfold Kapp in *. inversion H; inversion EXEC; subst. constructor.
    + inversion H.
      apply bs_Seq with c.
      * apply bs_Skip.
      * apply IHEXEC. unfold Kapp. reflexivity.
  - destruct k.
    + unfold Kapp in *. inversion H. inversion EXEC. subst. constructor. assumption.
    + unfold Kapp in *. inversion_clear H; subst.
      apply bs_Seq with ((s) [x <- n], i, o).
      * constructor. assumption.
      * auto.
  - destruct k.
    + unfold Kapp in *.
      inversion EXEC; subst.
      inversion_clear H; subst.
      constructor.
    + unfold Kapp in *. inversion H; subst.
      apply bs_Seq with ((s) [x <- z], i, o).
      * constructor.
      * apply IHEXEC. reflexivity.
  - destruct k.
    + unfold Kapp in *.
      inversion EXEC; subst.
      inversion_clear H; subst.
      constructor. assumption.
    + unfold Kapp in *. inversion H; subst.
      apply bs_Seq with ((s, i, z :: o)).
      * constructor. assumption.
      * apply IHEXEC. reflexivity.
  - destruct k. unfold Kapp in *.
    + inversion H; subst. apply IHEXEC. reflexivity.
    + inversion_clear H. apply SmokeTest.seq_assoc.  apply IHEXEC. unfold Kapp. reflexivity.
  - destruct k; unfold Kapp in *.
    +  inversion H; subst. apply bs_If_True; try assumption. apply IHEXEC. reflexivity.
    + inversion H; subst.
      apply if_seq_comm.
      apply bs_If_True; try assumption.
      apply IHEXEC. reflexivity.
  - destruct k. unfold Kapp in *. inversion H.
    + subst. apply bs_If_False.
      * assumption.
      * apply IHEXEC. reflexivity.
    + inversion H. subst. apply if_seq_comm. apply bs_If_False.
      * assumption.
      * apply IHEXEC. unfold Kapp in *. reflexivity.
  - destruct k. unfold Kapp in *. inversion H; subst.
    + apply SmokeTest.while_unfolds.
      apply bs_If_True.
        * assumption.
        * apply IHEXEC. reflexivity.
    + inversion H.
      apply while_unfold_seq.
      apply if_seq_comm.
      apply bs_If_True.
      * assumption.
      * unfold Kapp in *. apply SmokeTest.seq_assoc.
        apply IHEXEC. reflexivity.
  - destruct k.
    + unfold Kapp in *.
      inversion_clear H.
      inversion EXEC.
      apply bs_While_False.
      assumption.
    + unfold Kapp in *.
      inversion_clear H.
      apply while_unfold_seq.
      apply if_seq_comm.
      apply bs_If_False.
      * assumption.
      * apply skip_left_elim.
        apply IHEXEC. reflexivity.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  eapply cps_bs_gen;
  eauto.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') :
  c == s ==> c'.
Proof.
  eapply cps_bs_gen;
  eauto.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1;
  destruct k2.
  {
    auto.
  }
  {
    destruct k3;
    inversion STEP.
  }
  {
    auto.
  }
  {
    destruct k3;
    constructor;
    auto.
  }
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  inversion_clear STEP.
  generalize dependent k.
  generalize dependent c3.
  induction EXEC;
  intros.
  {
    constructor.
    assumption.
  }
  {
    econstructor;
    eassumption.
  }
  {
    econstructor.
    eassumption.
  }
  {
    econstructor;
    eassumption.
  }
  {
    econstructor.
    apply IHEXEC1.
    destruct k.
    {
      unfold Kapp.
      apply IHEXEC2.
      assumption.
    }
    {
      unfold Kapp.
      econstructor.
      unfold Kapp.
      auto.
    }
  }
  {
    econstructor;
    auto.
  }
  {
    econstructor 8;
    eauto.
  }
  {
    econstructor.
    assumption.
    apply IHEXEC1.
    destruct k.
    { auto. }
    {
      constructor.
      auto.
    }
  }
  {
    econstructor 10;
    assumption.
  }
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont;
  eauto.
  repeat constructor.
Qed.
