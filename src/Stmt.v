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
Proof. apply (H Hole). Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. exists ((Id 1) ::= Nat 42), ((Id 1) ::= Nat 56). split.
  - split; intro.
    + destruct H. dependent destruction H. econstructor. eapply bs_Assign. apply bs_Nat.
    + destruct H. dependent destruction H. econstructor. eapply bs_Assign. apply bs_Nat.
  - unfold not. intro. 
    specialize (H (SeqL Hole (WRITE (Var (Id 1)))) nil ([42%Z])). destruct H.
    assert (<| SeqL Hole (WRITE (Var (Id 1))) <~  Id 1 ::= Nat 56 |> [] => ([42%Z]) -> False) as contra.
    + intro. repeat dependent destruction H1. dependent destruction H1_.
      dependent destruction H1_0. dependent destruction VAL0. dependent destruction VAR.
      inversion VAL. contradiction.
    + apply contra. apply H. econstructor. econstructor.
      * apply bs_Assign. apply bs_Nat.
      * apply bs_Write. apply bs_Var. apply st_binds_hd.
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
  Proof. split; intros; seq_inversion; seq_inversion; seq_apply. Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. split; intros.
    - inversion H. subst.
      + apply bs_If_True. assumption. seq_apply.
      + apply bs_If_False. assumption. apply bs_Skip.
    - inversion H. subst.
      + seq_inversion. apply (bs_While_True s0 i o c'0 c' e s CVAL STEP1 STEP2).
      + inversion STEP. subst. apply (bs_While_False s0 i o e s CVAL).
    Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof. dependent induction EXE.
    - specialize (IHEXE2 e s st i o). apply IHEXE2; reflexivity.
    - apply CVAL.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. split; intros.
    - destruct c' as [p o']. destruct p as [st' i'].
      specialize (while_false (Nat 1) SKIP st' i' o' c H). intros. inversion H0.
    - inversion H; subst; inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof. split; intros.
    - dependent induction H.
      + eapply bs_While_True. 
        * apply CVAL.
        * apply EQ. apply H.
        * eapply IHbs_int2. apply EQ. reflexivity.
      + apply bs_While_False. apply CVAL.
    - dependent induction H.
      + eapply bs_While_True.
        * apply CVAL.
        * apply EQ. apply H.
        * eapply IHbs_int2. apply EQ. reflexivity.
      + apply bs_While_False. apply CVAL.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. unfold not. intros. dependent induction H.
    - apply (IHbs_int2 s). reflexivity.
    - inversion CVAL.
  Qed.

End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof. split; intros.
  - seq_inversion. specialize (EQ c'0 c'). apply EQ in STEP2. 
    eapply bs_Seq. apply STEP1. apply STEP2.
  - seq_inversion. specialize (EQ c'0 c'). apply EQ in STEP2.
    eapply bs_Seq. apply STEP1. apply STEP2.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof. split; intros.
  - seq_inversion. apply (EQ c c'0) in STEP1.
    eapply bs_Seq. apply STEP1. apply STEP2.
  - seq_inversion. apply (EQ c c'0) in STEP1.
    eapply bs_Seq. apply STEP1. apply STEP2.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. split; intros; inversion H; subst.
  - apply (bs_If_True s0 i o c' e s s2 CVAL STEP).
  - apply (EQ (s0, i, o) c') in STEP. apply (bs_If_False s0 i o c' e s s2 CVAL STEP).
  - apply (bs_If_True s0 i o c' e s s1 CVAL STEP).
  - apply (EQ (s0, i, o) c') in STEP. apply (bs_If_False s0 i o c' e s s1 CVAL STEP).
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. split; intros; inversion H; subst.
  - apply (EQ (s0, i, o) c') in STEP. apply (bs_If_True s0 i o c' e s2 s CVAL STEP).
  - apply (bs_If_False s0 i o c' e s2 s CVAL STEP).
  - apply (EQ (s0, i, o) c') in STEP. apply (bs_If_True s0 i o c' e s1 s CVAL STEP).
  - apply (bs_If_False s0 i o c' e s1 s CVAL STEP).
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. apply SmokeTest.while_eq. apply EQ. Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof. 
  split. apply (eq_congruence_seq_r s s1 s2 EQ).
  split. apply (eq_congruence_seq_l s s1 s2 EQ).
  split. apply (eq_congruence_cond_else e s s1 s2 EQ).
  split. apply (eq_congruence_cond_then e s s1 s2 EQ).
  apply (eq_congruence_while e s1 s2 EQ).
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
  dependent induction EXEC1 in c2; dependent destruction EXEC2; try reflexivity;
  try by_eval_deterministic; 
  try apply IHEXEC1_2; try rewrite (IHEXEC1_1 c'0); try assumption;
  try eval_zero_not_one; apply (IHEXEC1 c'0 EXEC2).
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma equivalent_states_update 
  (st st' : state Z)
  (x : id)
  (z : Z)
  (H: equivalent_states st st') :  equivalent_states ((st)[x <- z]) ((st')[x <- z]) .
Proof. 
  intro. intro. specialize (id_eq_dec id x) as H'.
  destruct H'. 
  - subst id. split; intros.
    inversion H0. apply st_binds_hd. contradiction.
    inversion H0. apply st_binds_hd. contradiction.
  - split; intro. 
  inversion H0. rewrite H1 in *. contradiction.
  apply st_binds_tl. assumption. apply H. assumption.
  inversion H0. rewrite H1 in *. contradiction.
  apply st_binds_tl. assumption. apply H. assumption.
Qed.

Lemma equivalent_states_eval
  (s1 s2 : state Z)
  (HE : equivalent_states s1 s2)
  (e : expr) (z : Z)
  (H : [|e|] s1 => z) : [|e|] s2 => z.
Proof. induction H; intros.
  apply bs_Nat.
  apply bs_Var. apply HE. apply VAR.
  all: try by econstructor; try apply (IHeval1 HE); try apply (IHeval2 HE).
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof. remember (st1, i, o). remember (st2, i', o'). generalize i o i' o' st1 st2 st1' HE1 Heqp Heqp0. 
       clear Heqp0 Heqp HE1 st1' st2 st1 o' i' o i. 
  induction H; intros.
  subst. inversion Heqp0. subst. exists st1'. split. apply HE1. apply bs_Skip.
  all: inversion Heqp; inversion Heqp0; subst.
  - exists (st1' [x <- z]). split. apply equivalent_states_update. apply HE1. apply bs_Assign.
    apply equivalent_states_eval with st1. apply HE1. apply VAL.
  - exists (st1' [x <- z]). split. 
    apply equivalent_states_update. apply HE1. apply bs_Read.
  - exists st1'. split. 
    apply HE1. 
    apply bs_Write. apply equivalent_states_eval with st2. apply HE1. apply VAL.
  - destruct c'. destruct p. 
    assert ((s, l0, l) = (s, l0, l)). reflexivity. 
    destruct (IHbs_int1 i o l0 l st1 s st1' HE1 H1 H3). destruct H4. 
    destruct (IHbs_int2 l0 l i' o' s st2 x H4 H3 H2). destruct H6. 
    exists x0. split. apply H6. apply bs_Seq with (x, l0, l). apply H5. apply H7.
  - destruct (IHbs_int i0 o0 i' o' st1 st2 st1' HE1 Heqp H0). destruct H1. 
    exists x. split. apply H1. 
    apply bs_If_True. apply equivalent_states_eval with st1. apply HE1. apply CVAL. apply H2.
  - destruct (IHbs_int i0 o0 i' o' st1 st2 st1' HE1 Heqp H0). destruct H1.
    exists x. split. apply H1. apply bs_If_False. apply equivalent_states_eval with st1. apply HE1. apply CVAL. apply H2.
  - destruct c'. destruct p. 
    assert ((s0, l0, l) = (s0, l0, l)). reflexivity. 
    destruct (IHbs_int1 i0 o0 l0 l st1 s0 st1' HE1 Heqp H2). destruct H3. 
    destruct (IHbs_int2 l0 l i' o' s0 st2 x H3 H2 H1). destruct H5. 
    exists x0. split. apply H5. apply bs_While_True with (x, l0, l). 
    apply equivalent_states_eval with st1. apply HE1. apply CVAL. apply H4. apply H6.
  - exists st1'. split. apply HE1. apply bs_While_False. apply equivalent_states_eval with st2. apply HE1. apply CVAL.
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
  Proof. dependent induction s; dependent destruction EXEC1; dependent destruction EXEC2;
    try reflexivity;
    try by_eval_deterministic;
    try (specialize (IHs1 _ _ _ EXEC1 EXEC2); inversion IHs1);
    try reflexivity; 
    eval_zero_not_one.
  Qed. 
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof. dependent induction STEP1; dependent destruction STEP2;
    specialize (ss_int_step_deterministic _ _ _ _ H H0); intros; inversion H1.
    reflexivity. subst. apply (IHSTEP1 STEP2).
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. inversion STEP; subst.
    - apply bs_Skip.
    - apply bs_Assign. assumption.
    - apply bs_Read.
    - apply bs_Write. assumption.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof. dependent induction STEP1; eapply ss_int_Step.
    - eapply ss_Seq_Compl. apply H.
    - apply STEP2.
    - eapply ss_Seq_InCompl. apply H.
    - apply (IHSTEP1 STEP2).
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof. revert EXEC STEP. revert s' c c' c''. induction s; intros.
    1-4: inversion STEP.
    - inversion STEP.
      + specialize (ss_bs_base s1 c c' SSTEP). intro. seq_apply.
      + subst s'. inversion EXEC. specialize (IHs1 s1' c c' c'1 STEP1 SSTEP). seq_apply.
    - inversion STEP; subst.
      + apply bs_If_True. apply SCVAL. apply EXEC.
      + apply bs_If_False. apply SCVAL. apply EXEC.
    - dependent induction STEP. inversion EXEC; inversion STEP.
      + eapply bs_While_True. apply CVAL. apply STEP1. apply STEP2.
      + eapply bs_While_False. apply CVAL.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. split; intros.
    - dependent induction s.
      + constructor. inversion H. subst. eapply ss_Skip.
      + constructor. inversion H. subst. eapply ss_Assign. apply VAL.
      + constructor. inversion H. subst. eapply ss_Read.
      + constructor. inversion H. subst. eapply ss_Write. apply VAL.
      + inversion H. subst. specialize (IHs1 c c'0 STEP1). specialize (IHs2 c'0 c' STEP2).
        apply (ss_ss_composition c c' c'0 s1 s2 IHs1 IHs2).
      + inversion H. subst. eapply ss_int_Step. eapply ss_If_True. apply CVAL.
        apply (IHs1 (s, i, o) c' STEP). eapply ss_int_Step. eapply ss_If_False. apply CVAL. 
        apply (IHs2 (s, i, o) c' STEP).
      + dependent induction H.
        * eapply ss_int_Step. eapply ss_While. eapply ss_int_Step.
          eapply ss_If_True. apply CVAL.
          eapply ss_ss_composition. eapply IHs. apply H.
          apply (IHbs_int2 s IHs e). reflexivity.
        * eapply ss_int_Step. eapply ss_While. eapply ss_int_Step.
          eapply ss_If_False. apply CVAL.
          eapply ss_int_Base. eapply ss_Skip.
    - induction H.
      + apply (ss_bs_base s c c' H).
      + apply (ss_bs_step c c' c'' s s' H IHss_int).
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
  Proof. induction s. 
    - reflexivity.
    - simpl. rewrite (Hinv i). specialize (Renaming.re_rename_expr r r' Hinv e) as REH.
      rewrite REH. reflexivity.
    - simpl. rewrite (Hinv i). reflexivity.
    - simpl. specialize (Renaming.re_rename_expr r r' Hinv e) as REH.
      rewrite REH. reflexivity.
    - simpl. rewrite IHs1. rewrite IHs2. reflexivity.
    - simpl. specialize (Renaming.re_rename_expr r r' Hinv e) as REH.
      rewrite REH. rewrite IHs1. rewrite IHs2. reflexivity.
    - simpl. specialize (Renaming.re_rename_expr r r' Hinv e) as REH.
      rewrite REH. rewrite IHs. reflexivity.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. dependent destruction r. constructor. Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof. destruct r as [g bG]. destruct bG as [h [HG GH]]. dependent induction Hbs.
    - constructor.
    - constructor. rewrite <- Renaming.eval_renaming_invariance. apply VAL.
    - constructor.
    - constructor. rewrite <- Renaming.eval_renaming_invariance. apply VAL.
    - econstructor; eassumption.
    - eapply bs_If_True. apply Renaming.eval_renaming_invariance. apply CVAL. apply IHHbs.
    - eapply bs_If_False. apply Renaming.eval_renaming_invariance. apply CVAL. apply IHHbs.
    - eapply bs_While_True. apply Renaming.eval_renaming_invariance. apply CVAL.
      apply IHHbs1. apply IHHbs2.
    - eapply bs_While_False. apply Renaming.eval_renaming_invariance. apply CVAL.
  Qed.

  Theorem re_rename_conf : forall (r r' : Renaming.renaming) (Hinv: Renaming.renamings_inv r r') (c: conf), rename_conf r (rename_conf r' c) = c.
    intros. destruct c as ((st, i), o). simpl. rewrite Renaming.re_rename_state. reflexivity. assumption.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof. destruct (Renaming.renaming_inv r) as [r' Hinv].
    rewrite <- (re_rename r' r Hinv s). rewrite <- (re_rename_conf r' r Hinv c). rewrite <- (re_rename_conf r' r Hinv c').
      apply renaming_invariant_bs. apply Hbs.
  Qed.
  
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof. split; intro.
    - inversion H. exists (Renaming.rename_state r x).
      apply (renaming_invariant_bs s r ([], i, []) (x, [], o) H0).
    - destruct (Renaming.renaming_inv r) as [r' Hinv]. destruct H as [st].
      specialize (renaming_invariant_bs_inv s r ([], i, []) (rename_conf r' (st, [], o))). intro.
      rewrite re_rename_conf in H0. specialize (H0 H). econstructor. apply H0. 
      assert (forall r r' (Hinv : Renaming.renamings_inv r r'), Renaming.renamings_inv r' r) as re_symm.
      + destruct r0 as [g0 bG0]. destruct bG0 as [h0 [HG0 GH0]]. unfold Renaming.renamings_inv. simpl. congruence.
      + apply re_symm. assumption.
  Qed.
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

Theorem if_fold (e: expr) (s1 s2 s : stmt) :
  (COND e THEN s1 ELSE s2 END ;; s) ~~~ (COND e THEN s1;; s ELSE s2;; s END).
Proof. split; intro; inversion H; subst.
  - inversion STEP1; subst.
    + apply bs_If_True. apply CVAL. eapply bs_Seq. apply STEP. apply STEP2.
    + apply bs_If_False. apply CVAL. eapply bs_Seq. apply STEP. apply STEP2.
  - inversion STEP. subst. eapply bs_Seq. apply bs_If_True. apply CVAL. apply STEP1. apply STEP2.
  - inversion STEP. subst. eapply bs_Seq. apply bs_If_False. apply CVAL. apply STEP1. apply STEP2.  
Qed.
    
Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof. generalize dependent S. induction EXEC; intros. 
  inversion DEF.
  all: destruct k; inversion DEF.
  all: try by (inversion EXEC; constructor).
  - eapply bs_Seq. apply bs_Skip. apply IHEXEC. reflexivity.
  - eapply bs_Seq. apply bs_Assign. apply CVAL. apply IHEXEC. reflexivity.
  - eapply bs_Seq. apply bs_Read. apply IHEXEC. reflexivity.
  - eapply bs_Seq. apply bs_Write. apply CVAL. apply IHEXEC. reflexivity.
  - apply IHEXEC. reflexivity.
  - apply SmokeTest.seq_assoc. apply IHEXEC. reflexivity.
  - apply bs_If_True. apply CVAL. apply IHEXEC. reflexivity.
  - apply if_fold. apply bs_If_True. apply CVAL. apply IHEXEC. reflexivity.
  - apply bs_If_False. apply CVAL. apply IHEXEC. reflexivity.
  - apply if_fold. apply bs_If_False. apply CVAL. apply IHEXEC. reflexivity.
  - apply SmokeTest.while_unfolds. apply bs_If_True. apply CVAL. apply IHEXEC. reflexivity.
  - assert (((st, i, o) == s ;; WHILE e DO s END ;; s0 ==> c') -> ((st, i, o) == WHILE e DO s END ;; s0 ==> c')) as while_ufoldl.
    + intro. inversion H. inversion STEP2. subst. eapply bs_Seq. eapply bs_While_True. apply CVAL.
      apply STEP1. apply STEP0. apply STEP3.
    + apply while_ufoldl. apply IHEXEC. reflexivity.
  - eapply bs_Seq. apply bs_While_False. apply CVAL. apply IHEXEC. reflexivity.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. eapply cps_bs_gen. eauto. reflexivity. Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. eapply cps_bs_gen. eauto. reflexivity. Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. dependent destruction k1.
  - dependent destruction k2.
    + apply STEP.
    + dependent destruction k3.
      all: inversion STEP.
  - dependent destruction k2.
    + apply STEP.
    + dependent destruction k3.
      all: (apply cps_Seq; assumption).
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. inversion STEP. subst. clear STEP. generalize dependent k. generalize c3.
  induction EXEC; intros.
  - apply cps_Skip. apply CSTEP.
  - eapply cps_Assign. apply VAL. apply CSTEP.
  - apply cps_Read. apply CSTEP.
  - eapply cps_Write. apply VAL. apply CSTEP.
  - apply cps_Seq. apply IHEXEC1. destruct k eqn:KD. 
    + eapply IHEXEC2. apply CSTEP.
    + apply cps_Seq. apply IHEXEC2. apply CSTEP.
  - apply cps_If_True. apply CVAL. apply IHEXEC. apply CSTEP.
  - apply cps_If_False. apply CVAL. apply IHEXEC. apply CSTEP.
  - apply cps_While_True. apply CVAL. apply IHEXEC1. destruct k eqn:KD.
    + eapply IHEXEC2. apply CSTEP.
    + eapply cps_Seq. apply IHEXEC2. apply CSTEP.
  - apply cps_While_False. apply CVAL. apply CSTEP.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. eapply bs_int_to_cps_int_cont. 
    apply EXEC. apply cps_Skip. apply cps_Empty.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
