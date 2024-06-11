Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

Require Import Coq.Program.Equality.

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
  unfold contextual_equivalent in *.
  unfold eval_equivalent in *.
  intros.

  specialize H with Hole i o.
  simpl in H.
  auto.
Qed.

Definition contra1 : stmt := (Id 0 ::= Nat 0).
Definition contra2 : stmt := (Id 0 ::= Nat 1).

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists contra1, contra2.
  split.
  - unfold eval_equivalent, eval.
    split; intros;
      destruct H;
      inversion H; subst;
      inversion VAL; subst.
    + exists  [(Id 0, 1%Z)].
      unfold contra2.
      repeat constructor.
    + exists [(Id 0, 0%Z)].
      unfold contra1.
      repeat constructor.
  - unfold not, eval_equivalent, contextual_equivalent.
    intros.
    unfold contra1, contra2 in *.
    specialize H with (SeqL Hole (WRITE (Var (Id 0)))).
    unfold eval_equivalent in *.
    unfold eval in H.
    simpl in H.
    specialize (H ([]) ([0%Z])).

    destruct H.
    assert (HA: (exists st : state Z, bs_int ((Id 0 ::= Nat 1);; WRITE (Var (Id 0))) ([], [], []) (st, [], [0%Z])) -> False).
      { intros.
        destruct H1.
        inversion H1. subst.
        inversion STEP1. subst. unfold update in STEP2, STEP1.
        inversion VAL. subst.
        inversion STEP2. subst.
        inversion VAL0.
        inversion VAR. subst. apply H10. reflexivity. }

    assert (HA': exists st : state Z, bs_int ((Id 0 ::= Nat 0);; WRITE (Var (Id 0))) ([], [], []) (st, [], [0%Z])).
      { exists [(Id 0, 0%Z)].
        econstructor; repeat constructor. }

    apply H in HA'.
    apply HA in HA'.
    assumption.
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
    intros c c'.
    split.
    - intros H.
      seq_inversion.
      seq_inversion.
      apply bs_Seq with c'1.
      + assumption.
      + apply bs_Seq with c'0.
        { assumption. }
        { assumption. }
    - intros H.
      seq_inversion.
      seq_inversion.
      apply bs_Seq with c'1.
      2: assumption.
      apply bs_Seq with c'0; assumption.
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

Inductive while_halt : conf -> expr -> stmt -> conf -> Prop :=
    | wi_Step  : forall
      (st : state Z)
      (i o : list Z)
      (c' c'' : conf)
      (e : expr)
      (s : stmt)
      (CVAL  : [| e |] st => Z.one)
      (STEP  : (st, i, o) == s ==> c')
      (WSTEP: while_halt c' e s c''),
    let c := (st, i, o) in while_halt c e s c''
  | wi_Base : forall
      (st : state Z)
      (i o : list Z)
      (e : expr)
      (s : stmt)
      (CVAL : [| e |] st => Z.zero),
      while_halt (st, i, o) e s (st, i, o)
    .

  Lemma while_halt_iff: forall c c' e s,
    while_halt c e s c' <-> c == WHILE e DO s END ==> c'.
  Proof.
    split.
    - intros H. induction H.
      + apply bs_While_True with c'; assumption.
      + apply bs_While_False. assumption.
    - remember (WHILE e DO s END) as cw eqn: Ecw.
      intros Hcw.
      induction Hcw; inversion Ecw; subst.
      + assert (HR: WHILE e DO s END = WHILE e DO s END). { reflexivity. }
        apply IHHcw2 in HR.
        apply wi_Step with c'; assumption.
      + apply wi_Base; assumption.
  Qed.

  Lemma while_ind_false: forall c e s i o st,
    while_halt c e s (st, i, o) -> [| e |] st => Z.zero.
  Proof.
    intros c e s i o st.
    (* remember (while_halt c e s (st, i, o)) as cw eqn: HEcw. *)
    remember (st, i, o) as stT eqn: HEstT.
    (* intros H. rewrite HEcw in H. *)
    intros H.
    induction H.
    1: { apply (IHwhile_halt HEstT). }
    1: { injection HEstT as HE; subst. assumption. }
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    apply while_halt_iff in EXE.
    apply while_ind_false in EXE.
    assumption.
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    split.
    - intros H.
      apply while_halt_iff in H.
      destruct c' eqn: Hce. destruct p eqn: Hpe.
      apply (while_ind_false) in H.
      inversion H.
    - intros H.
      inversion H; subst;
      inversion CVAL.
  Qed.

  Lemma while_eq_impl (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
    (* c == s1 ==> c' <-> c == s2 ==> c'. *)
    forall c c',
      c == WHILE e DO s1 END ==> c' ->
        c == WHILE e DO s2 END ==> c'.
  Proof.
  unfold bs_equivalent in *.
    intros c c'.
    intros H.
      remember (WHILE e DO s1 END) as ws1 eqn: Hews1.
      induction H; inversion Hews1; subst.
      { apply bs_While_True with c'.
        - assumption.
        - apply EQ in H. assumption.
        - apply IHbs_int2. reflexivity. }
      { apply bs_While_False. assumption. }
  Qed.

  Lemma bs_eq_comm (s1 s2: stmt):
    s1 ~~~ s2 -> s2 ~~~ s1.
  Proof.
    intros H.
    unfold bs_equivalent in *.
    intros c c'.
    split; intros H'; apply H in H'; assumption.
  Qed.

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    split; apply while_eq_impl;
      try assumption;
      try (now apply bs_eq_comm; assumption ).
  Qed.

  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    unfold not.
    intros H.
    apply while_halt_iff in H.
    destruct c' in H.
    destruct p in H.
    apply while_ind_false in H.
    inversion H.
  Qed.

End SmokeTest.

(* Semantic equivalence is a congruence *)
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

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent.
  intros c c'.
  split; intros H; inversion H; subst.
  1, 3: apply bs_If_True; try assumption; apply EQ; assumption.
  all: apply bs_If_False; assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  unfold bs_equivalent.
  intros c c'.

  remember (WHILE e DO s1 END) as wh1 eqn: HEwh1.
  remember (WHILE e DO s2 END) as wh2 eqn: HEwh2.

  split; intros H; induction H; inversion HEwh1; inversion HEwh2; subst.
  (* TODO duplication *)
  - apply EQ in H.
    assert (HR: WHILE e DO s1 END = WHILE e DO s1 END ). { reflexivity. }
    apply IHbs_int2 in HR.
    apply bs_While_True with c'; assumption.
  - apply bs_While_False; assumption.
  - apply EQ in H.
    assert (HR: WHILE e DO s2 END = WHILE e DO s2 END ). { reflexivity. }
    apply IHbs_int2 in HR.
    apply bs_While_True with c'; assumption.
  - apply bs_While_False; assumption.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  repeat split;

  try apply eq_congruence_seq_r;
  try apply eq_congruence_seq_l;
  try apply eq_congruence_cond_else;
  try apply eq_congruence_cond_then;
  try apply eq_congruence_while;

  try assumption;
  try (apply SmokeTest.bs_eq_comm; assumption).
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
  generalize dependent c.
  generalize dependent c1.
  generalize dependent c2.

  induction s.
  - intros c1 c2 c H1 H2. inversion H1. inversion H2.
    rewrite <- H3. rewrite <- H5.
    reflexivity.
  - intros c2 c1 c H1 H2.
    inversion H1; inversion H2; subst.
    inversion H8; subst.
    destruct (eval_deterministic _ _ _ _ VAL VAL0).
    reflexivity.
  - intros c2 c1 c H1 H2.
    inversion H1. inversion H2; subst. inversion H6; subst. reflexivity.
  - intros c2 c1 c H1 H2. inversion H1. inversion H2; subst. inversion H6; subst.
    destruct (eval_deterministic _ _ _ _ VAL VAL0). reflexivity.
  - intros c2 c1 c H1 H2.
    inversion H1.
    inversion H2.
    subst.
    destruct (IHs1 _ _ _ STEP1 STEP0).
    destruct (IHs2 _ _ _ STEP2 STEP3).
    reflexivity.
  - intros c2 c1 c H1 H2.
    inversion H1. inversion H2; subst; inversion H10; subst.
    { destruct (IHs1 _ _ _ STEP STEP0).
      reflexivity. }
    { assert (Z.one = Z.zero).
      { apply (eval_deterministic _ _ _ _ CVAL CVAL0). }
      discriminate H. }
    { inversion H2. inversion H10. subst. inversion H10. subst.
      { assert (Z.one = Z.zero).
      { apply (eval_deterministic _ _ _ _ CVAL0 CVAL). } discriminate H0. }
      { subst. inversion H10. subst.
        apply (IHs2 c2 c1 (s, i, o)); assumption. } }
  - intros c2 c1 c H1.
    generalize dependent c2.
    apply SmokeTest.while_halt_iff in H1.
    induction H1.
    + intros c2 H2. apply IHwhile_halt with c2 in IHs.
      { assumption. }
      { clear IHwhile_halt. inversion H2; subst.
        { assert (c'0 = c' ). { apply IHs with (st, i, o); assumption. }
          rewrite <- H. assumption. }
        { assert (Z.one = Z.zero). { apply (eval_deterministic _ _ _ _ CVAL CVAL0).  }
          discriminate H. } }
    + intros c2 H2. inversion H2; subst.
        { assert (Z.one = Z.zero). { apply (eval_deterministic _ _ _ _ CVAL0 CVAL).  }
          discriminate H. }
        { reflexivity. }
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma eq_st_result (e: expr) st1 st2:
  equivalent_states st1 st2 -> forall z, [|e|] st1 => z -> [|e|] st2 => z.
Proof.
  intros.
  induction H0; (try now econstructor; auto).
  + constructor. apply H. assumption.
Qed.

Lemma eq_st_result' (e: expr) st1 st2:
  equivalent_states st1 st2 -> forall z1 z2, [|e|] st1 => z1 -> [|e|] st2 => z2 -> z1 = z2.
Proof.
  intros.
  remember (eq_st_result e st1 st2 H z1 H0) as HE.
  clear HeqHE.
  destruct (eval_deterministic e st2 z2 z1 H1 HE).
  reflexivity.
Qed.

Lemma st_eq_equiv st1 st2 : st1 = st2 -> equivalent_states st1 st2.
Proof.
  intros. inversion H.
  unfold equivalent_states, Expr.equivalent_states.
  intros. reflexivity.
Qed.

Lemma st_assign_equiv st1 st2 v i : equivalent_states st1 st2 ->
  equivalent_states (st1 [i <- v]) (st2 [i <- v]).
Proof.
  unfold equivalent_states, Expr.equivalent_states in *.
  intros.

  split; intros; inversion H0; subst;
    try constructor;
    try auto;
      apply H; assumption.
Qed.

Definition equivalent_conf (c1 c2: conf): Prop.
  destruct c1 as [[st1 i1] o1].
  destruct c2 as [[st2 i2] o2].

  exact (equivalent_states st1 st2 /\ i1 = i2 /\ o1 = o2).
Defined.

Lemma conf_equiv_state_equiv st1 st2 i1 i2 o1 o2:
  equivalent_conf (st1, i1, o1) (st2, i2, o2) -> equivalent_states st1 st2.
Proof.
  intros.
  inversion H.
  assumption.
Qed.

Lemma conf_eq_equiv c1 c2 : c1 = c2 -> equivalent_conf c1 c2.
Proof.
  intros. inversion H.
  destruct c2 as [[st i] o].

  unfold equivalent_conf, equivalent_states.
  split.
    - intros. apply st_eq_equiv. reflexivity.
    - auto.
Qed.

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
      (* TODO what about big step expr eval *)
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
    generalize dependent c.
    generalize dependent c'.
    generalize dependent c''.

    induction s; intros c'' c' c H1 H2; inversion H1; inversion H2; subst.
    - subst. reflexivity.
    - inversion H8. subst. destruct (eval_deterministic _ _ _ _ SVAL SVAL0). reflexivity.
    - inversion H6; subst. reflexivity.
    - inversion H6; subst. destruct (eval_deterministic _ _ _ _ SVAL SVAL0). reflexivity.
    - assert (H'': ((None : option stmt), c'0) = (None, c'1)).
       { apply IHs1 with c; assumption. }
      inversion H''. subst. reflexivity.
    - assert (HR: ((Some s1', c'1)) = ((None, c'0))).
      { apply IHs1 with c; assumption. }
      discriminate HR.
    - assert (HR: ((Some s1', c'0)) = ((None, c'1))).
      { apply IHs1 with c; assumption. }
      discriminate HR.
    - assert (HR: ((Some s1', c'0)) = ((Some s1'0, c'1))).
      { apply IHs1 with c; assumption. }
      inversion HR; subst. reflexivity.
    - inversion H10; subst. reflexivity.
    - inversion H10. subst.
      assert( Z.one = Z.zero).
      { apply (eval_deterministic _ _ _ _ SCVAL SCVAL0). }
      discriminate H.
    - inversion H10. subst.
      assert( Z.zero = Z.one).
      { apply (eval_deterministic _ _ _ _ SCVAL SCVAL0). }
      discriminate H.
    - inversion H10; subst. reflexivity.
    - reflexivity.
  Qed.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''.

    induction STEP1.
    - intros c'' H'.
      inversion H'.

      * assert ((None: option stmt, c') = (None, c'')).
          { apply (ss_int_step_deterministic _ _ _ _ H H0). }
        inversion H4. reflexivity.
      * assert ((None: option stmt, c') = (Some s', c'0)).
          { apply (ss_int_step_deterministic _ _ _ _ H H0). }
        inversion H5.
    - intros c''' H'.
      inversion H'. subst.
      * assert ((Some s', c') = (None, c''')).
        { apply (ss_int_step_deterministic _ _ _ _ H H0). }
        discriminate H1.
      * subst.
        assert ((Some s', c') = (Some s'0, c'0)).
        { apply (ss_int_step_deterministic _ _ _ _ H H0). }
        inversion H2. subst.
        apply IHSTEP1.
        assumption.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    induction s; try ( now inversion STEP; subst; constructor).
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'.
  Proof.
  generalize dependent s2.
  generalize dependent c'.

  induction STEP1.

  - intros c'' s2 H'.

    assert ( c -- s;; s2 --> (Some s2, c')).
      { constructor. assumption. }
    assert (c -- s -->> c').
      { constructor. assumption. }

    apply (ss_int_Step) with s2 c'; assumption.
  - intros cg s2 H'.

    assert (c -- s -->> c'').
      { apply (ss_int_Step) with s' c'; assumption. }
    assert( c -- s;; s2 --> (Some (s';; s2), c')).
      { constructor. assumption. }

    apply ss_int_Step with (s';; s2) c'.
    + assumption.
    + apply IHSTEP1; assumption.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent s'.
    generalize dependent c.
    generalize dependent c'.
    generalize dependent c''.

    induction s; intros c'' c' c s' H H'; try now inversion H.
    - inversion H; subst.
      + assert (c == s1 ==> c').
          { apply ss_bs_base. assumption. }
        apply bs_Seq with c'; assumption.
      + inversion H'. subst.
        assert (c == s1 ==> c'0).
          { apply IHs1 with c' s1'; assumption. }
        apply bs_Seq with c'0; assumption.
    - inversion H; subst; inversion H'; subst; constructor; assumption.
    - inversion H. rewrite <- H4 in H'. subst. inversion H'; subst.
      + inversion H. apply SmokeTest.while_unfolds. assumption.
      + apply SmokeTest.while_unfolds. assumption.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    generalize dependent c.
    generalize dependent c'.

    split.
    - intros H. induction H; subst;
        try now constructor; constructor.
        + apply ss_ss_composition with c'; assumption.
        + apply (ss_int_Step (COND e THEN s1 ELSE s2 END) s1 (s, i, o) (s, i, o)).
          * constructor. assumption.
          * assumption.
        + apply (ss_int_Step (COND e THEN s1 ELSE s2 END) s2 (s, i, o) (s, i, o)).
          * constructor. assumption.
          * assumption.
        + apply (ss_int_Step (WHILE e DO s END) (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (st, i, o) (st, i, o) c'').
          * constructor.
          * apply (ss_int_Step (COND e THEN s;; (WHILE e DO s END) ELSE SKIP END) (s;; (WHILE e DO s END)) _ (st, i, o) _).
            { constructor. assumption. }
            { apply ss_ss_composition with c'; assumption. }
        + apply (ss_int_Step (WHILE e DO s END) (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (st, i, o) (st, i, o) _).
          * constructor.
          * apply (ss_int_Step (COND e THEN s;; (WHILE e DO s END) ELSE SKIP END) (SKIP) _ (st, i, o) _).
            { constructor. assumption. }
            { constructor. constructor. }
    - intros H.
      induction H.
      + apply ss_bs_base. assumption.
      + apply (ss_bs_step _ _ _ _ _ H IHss_int).
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

  Lemma re_rename
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (s    : stmt) : rename r (rename r' s) = s.
  Proof.
    dependent induction s;
    try reflexivity;
    (try now simpl; (try rewrite Hinv; try rewrite Expr.Renaming.re_rename_expr); reflexivity).
    * simpl.
      rewrite Expr.Renaming.re_rename_expr.
      { rewrite Hinv. reflexivity. }
      assumption.
    * simpl. rewrite Expr.Renaming.re_rename_expr. reflexivity. assumption.
    * simpl. rewrite IHs1; rewrite IHs2. reflexivity.
    * simpl. rewrite IHs1, IHs2. rewrite Expr.Renaming.re_rename_expr. reflexivity. assumption.
    * simpl. rewrite IHs, Expr.Renaming.re_rename_expr. reflexivity.
      assumption.
  Qed.

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    simpl. destruct r. reflexivity.
  Qed.

  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    dependent induction Hbs.
    - constructor.
    - simpl. destruct r. simpl. constructor.
      apply Expr.Renaming.eval_renaming_invariance. assumption.
    - simpl. destruct r. simpl. constructor.
    - simpl. destruct r. simpl. constructor.
      apply Expr.Renaming.eval_renaming_invariance. assumption.
    - simpl. econstructor; eassumption.
    - simpl. constructor.
      { apply Expr.Renaming.eval_renaming_invariance. assumption. }
      assumption.
    - simpl. apply bs_If_False. apply Expr.Renaming.eval_renaming_invariance.
      { assumption. }
      assumption.
    - simpl. econstructor.
      { apply Expr.Renaming.eval_renaming_invariance. assumption. }
      { eassumption. }
      assumption.
    - apply bs_While_False. apply Expr.Renaming.eval_renaming_invariance. assumption.
  Qed.

  Lemma state_rename st st' r: Renaming.rename_state r st = Renaming.rename_state r st' -> st = st'.
  Proof.
    intros.

    destruct (Expr.Renaming.renaming_inv r).
    eapply f_equal in H.
    do 2 erewrite Expr.Renaming.re_rename_state in H.
    assumption.
    (* TODO syntax error *)
    (* *: eassumption. *)
    - eassumption.
    - eassumption.
    - eassumption.
  Qed.

  Lemma conf_rename c c' r : rename_conf r c = rename_conf r c' -> c = c'.
  Proof.
    unfold rename_conf.
    destruct c, p.
    destruct c', p.
    intros.
    inversion H. subst.
    f_equal.
    f_equal.

    eapply state_rename.
    eauto.
  Qed.

  Lemma update_rename (r: renaming) s0 s i z:
  update Z (Renaming.rename_state r s0) (Renaming.rename_id r i) z = Renaming.rename_state r s ->
  s = (i, z)  :: s0.
  Proof.
    intros.
    destruct (Renaming.renaming_inv r).

    simpl in H.

    eapply state_rename with (r := r).
    symmetry.

    simpl.
    destruct r.
    auto.
  Qed.

  Lemma conf_is_conf_renaming c r: exists c', c = rename_conf r c'.
  Proof.
  destruct c. destruct p.
  destruct (Expr.Renaming.renaming_inv2 r).
  exists (rename_conf x (s, l0, l)).
  simpl.
  rewrite Renaming.re_rename_state.
  reflexivity.
  auto.
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
  Proof.
    assert (HA: Renaming.rename_state r ([]) = []). { reflexivity. }

    unfold eval_equivalent, eval.
    split; intros.
    - destruct H. exists (Renaming.rename_state r x).

      rewrite <- HA.
      destruct (Renaming.renaming_inv r).
      eapply renaming_invariant_bs_inv with (r := x0).

      rewrite re_rename.
      simpl.
      rewrite (Renaming.re_rename_state).
      assumption.
      auto. auto.
    - destruct H.
      destruct (Renaming.renaming_inv_inv r).

      exists (Renaming.rename_state x0 x).
      eapply renaming_invariant_bs_inv with r.
      simpl.
      rewrite (Renaming.re_rename_state).
      assumption.
      destruct H0.
      assumption.
  Qed.

End Renaming.

(* CPS semantics *)
Inductive cont : Type :=
| KEmpty : cont
| KStmt  : stmt -> cont.

Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty, _       ) => r
  | (_     , KEmpty  ) => l
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

Ltac cps_bs_gen_helper k H HH :=
  destruct k eqn:K; subst; inversion H; subst;
  [inversion EXEC; subst | eapply bs_Seq; eauto];
  apply HH; auto.

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
  (* remember ((k) |- c -- S1 --> (c')) as scont eqn: Econt. *)
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
  apply cps_bs_gen with !s1 !s2.
  - assumption.
  - reflexivity.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') :
  c == s ==> c'.
Proof.
generalize dependent c'.
generalize dependent c.

induction s; intros c c' STEP; inversion STEP; subst.
- inversion CSTEP; subst; constructor.
- inversion CSTEP; subst. constructor. assumption.
- inversion CSTEP. subst. constructor.
- inversion CSTEP. subst. constructor. auto.
- unfold Kapp in *. apply cps_bs. assumption.
- apply bs_If_True; [ assumption | auto ].
- apply bs_If_False; [ assumption | auto ].
- unfold Kapp in *.
  apply SmokeTest.while_unfolds.
  apply bs_If_True.
    + assumption.
    + apply cps_bs. assumption.
- inversion CSTEP. apply bs_While_False. assumption.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  inversion STEP; subst.
  6: { destruct k2; destruct k3; unfold Kapp in *;
        try now auto.
        - constructor. unfold Kapp in *. assumption.
        - constructor. unfold Kapp in *. assumption.
        }

  - destruct k2.
    + unfold Kapp in *. assumption.
    + destruct k3; inversion H0.
  - destruct k2; unfold Kapp in *.
    + assumption.
    + destruct k3.
      * unfold Kapp in *; constructor; unfold Kapp in *. assumption.
      * constructor. unfold Kapp in *. assumption.
  - destruct k2; destruct k3; unfold Kapp in *.
    + inversion  CSTEP; subst. auto.
    + assumption.
    + constructor; unfold Kapp in *; assumption.
    + constructor; unfold Kapp in *; assumption.
  - destruct k2, k3. unfold Kapp in *.
    + assumption.
    + assumption.
    + constructor. unfold Kapp in *. assumption.
    + constructor. unfold Kapp in *. assumption.
  - destruct k2, k3; unfold Kapp in *;
    try now assumption.
    all: constructor; unfold Kapp; assumption.
  - destruct k2, k3; unfold Kapp in *;
    try now assumption.
    all: constructor; unfold Kapp; assumption.
  - destruct k2, k3; unfold Kapp in *;
    try now assumption.
    all: constructor; unfold Kapp; assumption.
  - destruct k2, k3; unfold Kapp in *;
    try now assumption.
    all: constructor; unfold Kapp; assumption.
  - destruct k2, k3; unfold Kapp in *;
    try now assumption.
    all: constructor; unfold Kapp; assumption.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  generalize dependent k.

  dependent induction EXEC; intros.
  5: {
    eapply cps_Seq.
    eapply IHEXEC1.
    destruct k.
    { compute.
      constructor.
      eapply IHEXEC2; eauto. }
    { constructor.
      eapply cps_cont_to_seq.
      compute.
      eapply IHEXEC2; eauto. } }
  - assumption.
  - econstructor; eauto. inversion STEP. subst. eauto.
  -  econstructor; eauto. inversion STEP. subst. eauto.
  -  econstructor; eauto. inversion STEP. subst. eauto.
  - econstructor; eauto.
  - eapply cps_If_False; eauto.
  - econstructor; eauto.
    inversion STEP. subst.
    eapply IHEXEC1.
    constructor.
    destruct k.
    { compute. eauto. }
    apply cps_cont_to_seq. compute. eauto.
  - eapply cps_While_False; eauto.
    inversion STEP. subst. eauto.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont. eauto. repeat constructor.
Qed.
