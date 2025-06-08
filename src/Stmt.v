Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

Require Import Coq.Program.Equality.
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
    unfold contextual_equivalent, eval_equivalent in *.
    intros i o. specialize (H Hole).
    simpl in H. apply H.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists (Id 2 ::= Nat 5), (Id 3 ::= Nat 7).
  split.
  - unfold eval_equivalent; intros; split; intros;
    inversion H; inversion H0; repeat econstructor.
  - intro H.
    specialize (H (SeqL (Hole) (WRITE (Var (Id 2))))).
    specialize (H ([]) ([5%Z])).
    destruct H as [H _].
    specialize (H ltac:(repeat econstructor)).
    inversion H.
    subst.
    inversion H0.
    subst.
    inversion STEP1.
    subst.
    inversion STEP2.
    subst.
    inversion VAL.
    subst.
    inversion VAL0.
    subst.
    inversion VAR.
    subst.
    inversion H7.
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
    unfold bs_equivalent; split; intros.
    - inversion H; subst.
      rename c'0 into c1.
      inversion STEP1; subst.
      rename c'0 into c2.
      apply bs_Seq with (c' := c2).
      + assumption.
      + apply bs_Seq with (c' := c1).
        * assumption.
        * assumption.
    - inversion H; subst.
      inversion STEP2; subst.
      apply bs_Seq with (c' := c'1).
      + apply bs_Seq with (c' := c'0).
        * assumption.
        * assumption.
      + assumption.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent; split; intros.
    - inversion H; subst.
      + eapply bs_If_True; eauto.
      + eapply bs_If_False; eauto.
    - inversion H; subst.
      + inversion STEP; subst.
        eapply bs_While_True; eauto.
      + inversion STEP; subst.
        eapply bs_While_False; eauto.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.  
    dependent induction EXE.  
    eapply (IHEXE2 e s st i o);  
    intuition. intuition.
  Qed.  
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent. split.
    intros. dependent induction H.
    inversion H. subst. apply IHbs_int2. intuition.
    inversion CVAL.
    intros. dependent induction H.
    all: inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent; intros; split; intro H;
    dependent induction H; try constructor; eauto;
    econstructor; eauto; apply EQ; eassumption.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. 
    intro H.
    remember (WHILE (Nat 1) DO s END) as loop eqn:Heqloop.
    induction H; try inversion Heqloop; subst.
    - inversion CVAL; subst.
      eapply IHbs_int2 .
      contradiction.
    - inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
    split; intros; seq_inversion; eapply bs_Seq; eauto; now apply EQ.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent; split; intros.
  - inversion H; subst.
    apply bs_Seq with (c' := c'0).
    + now apply EQ.
    + assumption.
  - inversion H; subst.
    apply bs_Seq with (c' := c'0).
    + now apply EQ.
    + assumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent; split; intros.
  - inversion H; subst.
    + apply bs_If_True; auto.
    + apply bs_If_False; auto.
      now apply EQ.
  - inversion H; subst.
    + apply bs_If_True; auto.
    + apply bs_If_False; auto.
      now apply EQ.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent; split; intros.
  - inversion H; subst.
    + apply bs_If_True; auto.
      now apply EQ.
    + apply bs_If_False; auto.
  - inversion H; subst.
    + apply bs_If_True; auto.
      now apply EQ.
    + apply bs_If_False; auto.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  eapply SmokeTest.while_eq. intuition.
Qed.


Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split; [apply eq_congruence_seq_r | 
          split; [apply eq_congruence_seq_l |
                  split; [apply eq_congruence_cond_else |
                          split; [apply eq_congruence_cond_then |
                                  apply eq_congruence_while]]]]; intuition.
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
  generalize dependent c2.
  induction EXEC1; intros; inversion EXEC2; subst; intuition;
  try (apply (eval_deterministic e s z z0) in VAL; subst; intuition; fail);
  try eval_zero_not_one.
  specialize (IHEXEC1_1 c'0 STEP1). subst c'0. 
  specialize (IHEXEC1_2 c2 STEP2). intuition.
  specialize (IHEXEC1_1 c'0 STEP). subst c'0.
  specialize (IHEXEC1_2 c2 WSTEP). intuition.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma eq_preserve (s1 s2 : state Z) (HEQ : equivalent_states s1 s2) (x : id) (n : Z) :
equivalent_states (s1 [x <- n]) (s2 [x <- n]).  
Proof.
  unfold equivalent_states, Expr.equivalent_states in *.
  intros e.
  split; intros H; 
    inversion H as [ | ? ? ? ? H']; subst;
    try constructor;
    try assumption.
  - apply HEQ; assumption.
  - apply HEQ; assumption.
Qed.

Lemma same_var (s1 s2 : state Z) (HEQ : equivalent_states s1 s2) (e : expr) (n : Z) (EVAL : [|e|] s1 => n) :
[|e|] s2 => n.
Proof.
  revert s2 HEQ.
  induction EVAL; intros s2 HE;
  match goal with
  | |- [| _ |] _ => _ =>
    solve [constructor
          | constructor; assumption
          | econstructor; [apply IHeval1 | apply IHeval2]; assumption
          | unfold equivalent_states in HE; constructor; apply HE; assumption
          | eauto]
  end.
Qed.

Lemma bs_equiv_states
    (s            : stmt)
    (i o i' o'    : list Z)
    (st1 st2 st1' : state Z)
    (HE1          : equivalent_states st1 st1')  
    (H            : (st1, i, o) == s ==> (st2, i', o')) :
    exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  remember (st1, i, o) as c1.
  remember (st2, i', o') as c2.
  revert i o i' o' st1 st2 st1' HE1 Heqc1 Heqc2.
  induction H; intros.
  
  (* Case 1: Skip *)
  - subst. inversion Heqc2. subst. clear Heqc2.
    exists st1'; split; trivial.

   (* Case 2: Assignment *)
  - inversion Heqc1; inversion Heqc2; subst.
    exists (st1' [x <- z]); split; auto.
    * apply eq_preserve; auto.
    * constructor. eauto using same_var.

  (* Case 3: Read *)
  - inversion Heqc1; inversion Heqc2; subst.
    exists (st1' [x <- z]); split; auto.
    * apply eq_preserve; auto.

  (* Case 4: Write *)
  - inversion Heqc1; inversion Heqc2; subst.
    exists st1'; split; intuition. apply bs_Write. eapply same_var; eauto.

  (* Case 5: Sequence *)
  - inversion Heqc1; inversion Heqc2; subst.
    destruct c' as [[stmid lmid] lmid'].
    edestruct IHbs_int1 as [st2' [HE2 Hbs1]]; eauto.
    edestruct IHbs_int2 as [st3' [HE3 Hbs2]]; eauto.

  (* Case 6: If-True *)
  - inversion Heqc1; inversion Heqc2; subst.
    edestruct IHbs_int as [st2' [HE2 Hbs]]; eauto.
    exists st2'; split; auto.
    apply bs_If_True; auto.
    eapply same_var; eauto.

  (* Case 7: If-False *)
  - inversion Heqc1; inversion Heqc2; subst.
    edestruct IHbs_int as [st2' [HE2 Hbs]]; eauto.
    exists st2'; split; auto.
    apply bs_If_False; auto.
    eapply same_var; eauto.

  (* Case 8: While-True *)
  - inversion Heqc1; inversion Heqc2; subst.
    destruct c' as [[stmid lmid] lmid'].
    edestruct IHbs_int1 as [st2' [HE2 Hbs1]]; eauto.
    edestruct IHbs_int2 as [st3' [HE3 Hbs2]]; eauto.
    exists st3'; split; auto.
    apply bs_While_True with (st2', lmid, lmid'); auto.
    eapply same_var; eauto.
    
  (* Case 9: While-False *)
  - inversion Heqc1; inversion Heqc2; subst.
    exists st1'; split; intuition. apply bs_While_False. eapply same_var; eauto.
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
    generalize dependent c'.
    induction EXEC2; intros;
    match goal with
    | [ H : _ -- _ --> _ |- _ ] => inversion H; subst; clear H
    end;
    auto;
    try (apply (eval_deterministic e s z z0) in SVAL; subst; auto);
    try (apply IHEXEC2 in SSTEP; inversion SSTEP; auto);
    try eval_zero_not_one.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''.
    induction STEP1; intros;
    inversion STEP2; subst;
    try (let step := fresh in
          assert (step := ss_int_step_deterministic _ _ _ _ H H0);
          inversion step;
          subst; intuition).
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
      dependent induction s; dependent destruction STEP; eauto using bs_int.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
      induction STEP1.
      apply ss_int_Step with (s2) (c'0).
      apply ss_Seq_Compl.
      eauto.
      intuition.
      apply IHSTEP1 in STEP2.
      assert (ss_int_step (Seq s s2) c (Some (Seq s' s2), c'0)).
      apply ss_Seq_InCompl.
      intuition.
      eapply ss_int_Step.
      all: eauto.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    induction s in c, c', c'', s', STEP, EXEC |- *;
    try (inversion STEP; subst; eauto using bs_If_True, bs_If_False, bs_While_False; fail).
    inversion STEP; subst.
    apply bs_Seq with (c' := c'); auto using ss_bs_base.
    inversion EXEC; subst.
    apply bs_Seq with (c' := c'0); intuition.
    eauto.
    inversion STEP; subst;
    inversion EXEC; subst;
    inversion STEP0; intuition;
    eauto using bs_While_True, bs_While_False.
  Qed.
  

    Theorem bs_ss_eq (s : stmt) (c c' : conf) :
        c == s ==> c' <-> c -- s -->> c'.
    Proof.
      split; intros.
      induction H as [ | | | | c c'' c' s1 s2 H1 IH1 H2 IH2 
                  | s i o e s1 s2 b Hval H IH 
                  | s i o e s1 s2 b Hval H IH
                  | st i o e s c'' c' b Hval H1 IH1 H2 IH2
                  | st i o e s b Hval]; intros.
      repeat constructor; intuition.
      repeat constructor; intuition.
      repeat constructor; intuition.
      repeat constructor; intuition.
      eapply ss_ss_composition.
      apply IH1.
      intuition.
      eapply ss_int_Step.
      apply ss_If_True.
      intuition.
      intuition.
      eapply ss_int_Step.
      apply ss_If_False.
      intuition.
      intuition.
      eapply ss_int_Step.
      apply ss_While.
      eapply ss_int_Step.
      apply ss_If_True.
      intuition.
      eapply ss_ss_composition.
      apply H1.
      apply H2.
      eapply ss_int_Step.
      apply ss_While.
      eapply ss_int_Step.
      apply ss_If_False. 
      intuition.
      repeat constructor.
      induction H as [c s H | c c' c'' s s' Hstep IH].
      apply ss_bs_base.
      intuition.
      eapply ss_bs_step.
      apply Hstep.
      apply IHIH.
    Qed.
  
End SmallStep.

Module Renaming.

  Definition renaming := Renaming.renaming.

  Definition rename_conf (r : renaming) (c : conf) : conf :=
    match c with
    | (st, i, o) => (Renaming.rename_state r st, i, o)
    end.
  
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
    induction s;
      simpl; auto.
    - rewrite Renaming.re_rename_expr; auto. congruence.
    - rewrite Hinv; reflexivity.
    - rewrite Renaming.re_rename_expr; congruence.
    - rewrite IHs1, IHs2; reflexivity.
    - rewrite Renaming.re_rename_expr. eauto. congruence. assumption.
    - rewrite Renaming.re_rename_expr. eauto. rewrite IHs. eauto. assumption.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    destruct r; simpl; reflexivity. 
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof. admit. Admitted.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    pose proof (Renaming.renaming_inv r) as [r' Hinv].
    eapply renaming_invariant_bs in Hbs.
    rewrite re_rename in Hbs.
    destruct c as [[st i] o], c' as [[st' i'] o'].
    destruct r as [f [g [Hinv1 Hinv2]]].
    simpl in Hbs.
    rewrite Renaming.re_rename_state in Hbs; intuition.
    rewrite Renaming.re_rename_state in Hbs; intuition.
    all: eapply Hinv.
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

Ltac cps_bs_gen_helper k H HH :=
  destruct k eqn:K; subst; inversion H; subst;
  [inversion EXEC; subst | eapply bs_Seq; eauto];
  apply HH; auto.
    
Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof.
  generalize dependent S.
  induction EXEC; intros.
  - discriminate DEF.
  - cps_bs_gen_helper k DEF bs_Skip.
  - cps_bs_gen_helper k DEF bs_Assign.
  - cps_bs_gen_helper k DEF bs_Read.
  - cps_bs_gen_helper k DEF bs_Write.
  - destruct k; inversion DEF; subst;
    [apply IHEXEC; intuition | apply SmokeTest.seq_assoc; apply IHEXEC; intuition].
  - destruct k; inversion DEF; subst;
    [apply bs_If_True; intuition | assert (step : bs_int (Seq s1 s0) (s, i, o) c')].
      apply IHEXEC; intuition.
      inversion step; subst; apply bs_Seq with (c'0); intuition .
  - destruct k; inversion DEF; subst;
    [ apply bs_If_False; intuition
    | assert (step : bs_int (Seq s2 s0) (s, i, o) c')].
      apply IHEXEC; intuition. 
      inversion step; subst; apply bs_Seq with (c'0); intuition.
  - destruct k; inversion DEF; subst.
    assert (step : bs_int (Seq s (While e s)) (st, i, o) c').
    apply IHEXEC; intuition.
    inversion step; subst. apply bs_While_True with (c'0); intuition.
    assert (step : bs_int (Seq s (Seq (While e s) s0)) (st, i, o) c').
    apply IHEXEC; intuition.
    inversion step; subst. inversion STEP2; subst. apply bs_Seq with (c'1).
    apply bs_While_True with (c'0); intuition. intuition.
    - cps_bs_gen_helper k DEF bs_While_False.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
   eapply cps_bs_gen; eauto.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
    eapply cps_bs_gen; eauto.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1, k2, k3; try solve [inversion STEP]; auto.
  all: simpl; constructor; assumption.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  dependent destruction STEP; generalize dependent k;
  dependent induction EXEC; intros; try solve [econstructor; eauto].
  all: econstructor; eauto; apply IHEXEC1; eauto;
        dependent destruction k; eauto using cps_cont_to_seq.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  apply bs_int_to_cps_int_cont with (c2 := c').
  intuition.
  econstructor;
  econstructor.
Qed.


(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)