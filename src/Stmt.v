Require Import List.
Import ListNotations.
Require Import Lia.

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
  (* Гипотеза H верна для ЛЮБОГО контекста. Специфицируем её контекстом Hole *)
  specialize (H Hole).
  (* Раскрываем определение plug для Hole, превращая (Hole <~ s) в просто s *)
  simpl in H.
  (* Теперь гипотеза H в точности совпадает с нашей целью *)
  assumption.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists (WRITE (Var (Id 0))), SKIP.
  split.
  - intros i o. split; intro H.
    + destruct H as [st Hbs].
      inversion Hbs; subst.
      inversion VAL; subst.
      inversion H2.
    + destruct H as [st Hbs].
      inversion Hbs; subst.
      assert (o = []) by (inversion Hbs; reflexivity).
      subst o.
      exists [].
      constructor.

  - intros Hc.
    specialize (Hc (SeqR (Id 0 ::= Num 1) Hole)).
    simpl in Hc.
    specialize (Hc [] [Z.one]).
    destruct Hc as [Hforward _].
    assert (Hrun : <| Id 0 ::= Num 1 ;; WRITE (Var (Id 0)) |> [] => [Z.one]). {
      exists [(Id 0, Z.one)].
      eapply bs_Seq.
      - eapply bs_Assign. constructor.
      - change (update Z [] (Id 0) Z.one) with [(Id 0, Z.one)].
        eapply bs_Write.
        constructor. constructor.
    }
    apply Hforward in Hrun.
    destruct Hrun as [st' Hskip].
    inversion Hskip; subst.
    inversion STEP1; subst.
    inversion STEP2; subst.
    discriminate.
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
    split; intro H.
    - seq_inversion. 
      seq_inversion. 
      seq_apply.
    - seq_inversion.
      seq_inversion.
      seq_apply.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent; intros c c'; split; intro H.
    - inversion H; subst; [econstructor 6 | econstructor 7]; eauto.
    - inversion H; subst.
      + seq_inversion. econstructor 8; eauto.
      + inversion STEP; subst. econstructor 9; eauto.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as wstmt eqn:Heqw.
    remember (st, i, o) as c' eqn:Heqc'.
    induction EXE; inversion Heqw; subst.
    - apply IHEXE2; reflexivity.
    - inversion Heqc'; subst.
      assumption.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros c c'.
    split; intro H.
    - destruct c' as [[st i] o].
      apply while_false in H.
      inversion H.
    - inversion H; subst;
      inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent in *.
    intros c c'.
    split; intro H.
    - remember (WHILE e DO s1 END) as wstmt eqn:Heqw.
      induction H; inversion Heqw; subst.
      + eapply bs_While_True.
        * eexact CVAL.
        * apply EQ. eexact STEP.
        * apply IHbs_int2. reflexivity.
      + eapply bs_While_False.
        eexact CVAL.
    - remember (WHILE e DO s2 END) as wstmt eqn:Heqw.
      induction H; inversion Heqw; subst.
      + eapply bs_While_True.
        * eexact CVAL.
        * apply EQ. eexact STEP.
        * apply IHbs_int2. reflexivity.
      + eapply bs_While_False.
        eexact CVAL.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro H.
    remember (WHILE (Nat 1) DO s END) as wstmt eqn:Heqw.
    induction H; inversion Heqw; subst.
    - apply IHbs_int2. reflexivity.
    - inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro H.
  - seq_inversion.
    eapply bs_Seq.
    + eexact STEP1.
    + apply EQ. eexact STEP2.
  - seq_inversion.
    eapply bs_Seq.
    + eexact STEP1.
    + apply EQ. eexact STEP2.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro H.
  - seq_inversion.
    eapply bs_Seq.
    + apply EQ. eexact STEP1.
    + eexact STEP2.
  - seq_inversion.
    eapply bs_Seq.
    + apply EQ. eexact STEP1.
    + eexact STEP2.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro H.
  - inversion H; subst.
    + eapply bs_If_True.
      * eexact CVAL.
      * eexact STEP.
    + eapply bs_If_False.
      * eexact CVAL.
      * apply EQ. eexact STEP.
  - inversion H; subst.
    + eapply bs_If_True.
      * eexact CVAL.
      * eexact STEP.
    + eapply bs_If_False.
      * eexact CVAL.
      * apply EQ. eexact STEP.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro H.
  - inversion H; subst.
    + eapply bs_If_True.
      * eexact CVAL.
      * apply EQ. eexact STEP.
    + eapply bs_If_False.
      * eexact CVAL.
      * eexact STEP.
  - inversion H; subst.
    + eapply bs_If_True.
      * eexact CVAL.
      * apply EQ. eexact STEP.
    + eapply bs_If_False.
      * eexact CVAL.
      * eexact STEP.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  unfold bs_equivalent in *; intros c c'; split; intro H.
  - remember (WHILE e DO s1 END) as wstmt eqn:Heqw.
    induction H; inversion Heqw; subst; [econstructor 8 | econstructor 9]; eauto; apply EQ; eauto.
  - remember (WHILE e DO s2 END) as wstmt eqn:Heqw.
    induction H; inversion Heqw; subst; [econstructor 8 | econstructor 9]; eauto; apply EQ; eauto.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  repeat split.
  - apply eq_congruence_seq_r; assumption.
  - apply eq_congruence_seq_l; assumption.
  - apply eq_congruence_cond_else; assumption.
  - apply eq_congruence_cond_then; assumption.
  - apply eq_congruence_while; assumption.
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
  generalize dependent c2; induction EXEC1; intros c2 EXEC2;
  inversion EXEC2; subst; try reflexivity;
  try by_eval_deterministic; try eval_zero_not_one.
  - assert (c' = c'0) by (apply IHEXEC1_1; assumption); subst c'0.
    apply IHEXEC1_2; assumption.
  - assert (c' = c'0) by (apply IHEXEC1_1; assumption); subst c'0.
    apply IHEXEC1_2; assumption.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma expr_equiv_eval (e : expr) (st1 st2 : state Z) (z : Z)
      (HE : equivalent_states st1 st2)
      (H : [| e |] st1 => z) :
  [| e |] st2 => z.
Proof.
  unfold equivalent_states in HE.
  eapply Expr.equivalent_states_eval; eauto.
Qed.

Lemma equiv_states_update (st1 st2 : state Z) (x : id) (z : Z)
      (HE : equivalent_states st1 st2) :
  equivalent_states (update Z st1 x z) (update Z st2 x z).
Proof.
  unfold equivalent_states, Expr.equivalent_states in *.
  intro id.
  eapply Expr.equivalent_states_update; eauto.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')  
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  generalize dependent st1'.
  induction H; intros st1'' HE1.
  - exists st1''. split; [assumption | econstructor].
  - exists (update Z st1'' x z). split.
    + apply equiv_states_update; assumption.
    + econstructor. eapply expr_equiv_eval; [eexact HE1 | eexact VAL].
  - exists (update Z st1'' x z). split.
    + apply equiv_states_update; assumption.
    + econstructor.
  - exists st1''. split; [assumption |].
    econstructor.
    + eapply expr_equiv_eval; [eexact HE1 | eexact VAL].
  - destruct (IHbs_int1 st1'' HE1) as [st2'' [HE2 STEP1]].
    destruct c' as [[st2 i0] o0].
    destruct (IHbs_int2 st2'' HE2) as [st3'' [HE3 STEP2]].
    exists st3''. split; [assumption |].
    econstructor; [eexact STEP1 | eexact STEP2].
  - destruct (IHbs_int st1'' HE1) as [st2'' [HE2 STEP']].
    exists st2''. split; [assumption |].
    eapply bs_If_True.
    + eapply expr_equiv_eval; [eexact HE1 | eexact CVAL].
    + eexact STEP'].
  - destruct (IHbs_int st1'' HE1) as [st2'' [HE2 STEP']].
    exists st2''. split; [assumption |].
    eapply bs_If_False.
    + eapply expr_equiv_eval; [eexact HE1 | eexact CVAL].
    + eexact STEP'].
  - destruct (IHbs_int1 st1'' HE1) as [st2'' [HE2 STEP1]].
    destruct c' as [[st2 i0] o0].
    destruct (IHbs_int2 st2'' HE2) as [st3'' [HE3 STEP2]].
    exists st3''. split; [assumption |].
    eapply bs_While_True.
    + eapply expr_equiv_eval; [eexact HE1 | eexact CVAL].
    + eexact STEP1.
    + eexact STEP2.
  - exists st1''. split; [assumption |].
    econstructor.
    eapply expr_equiv_eval; [eexact HE1 | eexact CVAL].
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
    generalize dependent c''.
    induction EXEC1; intros c'' EXEC2; inversion EXEC2; subst.
    - reflexivity.
    - by_eval_deterministic.
    - reflexivity.
    - by_eval_deterministic.
    - assert (Hstep: (None, c'0) = (None, c'1)) by (apply IHEXEC1; assumption).
      inversion Hstep; subst; reflexivity.
    - assert (Hstep: (None, c'0) = (Some s1', c'1)) by (apply IHEXEC1; assumption).
      inversion Hstep.
    - assert (Hstep: (Some s1', c'0) = (None, c'1)) by (apply IHEXEC1; assumption).
      inversion Hstep.
    - assert (Hstep: (Some s1'0, c'0) = (Some s1', c'1)) by (apply IHEXEC1; assumption).
      inversion Hstep; subst; reflexivity.
    - reflexivity.
    - eval_zero_not_one.
    - eval_zero_not_one.
    - reflexivity.
    - reflexivity.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''.
    induction STEP1; intros c'' STEP2.
    - inversion STEP2; subst.
      + assert (Hstep: (None, c') = (None, c'0)) by (eapply ss_int_step_deterministic; eauto).
        inversion Hstep; reflexivity.
      + assert (Hstep: (None, c') = (Some s', c'0)) by (eapply ss_int_step_deterministic; eauto).
        inversion Hstep.
    - inversion STEP2; subst.
      + assert (Hstep: (Some s', c') = (None, c'0)) by (eapply ss_int_step_deterministic; eauto).
        inversion Hstep.
      + assert (Hstep: (Some s', c') = (Some s'0, c'0)) by (eapply ss_int_step_deterministic; eauto).
        inversion Hstep; subst.
        apply IHSTEP1; assumption.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP; subst; constructor; assumption.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    generalize dependent s2.
    generalize dependent c'.
    induction STEP1; intros c' s2 STEP2.
    - eapply ss_int_Step.
      + eapply ss_Seq_Compl. eexact H.
      + eexact STEP2.
    - eapply ss_int_Step.
      + eapply ss_Seq_InCompl. eexact H.
      + apply IHSTEP1. assumption.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent c''.
    induction STEP; intros c'' EXEC.
    - assert (EXEC1: c == s1 ==> c') by (eapply ss_bs_base; eexact SSTEP).
      eapply bs_Seq.
      + eexact EXEC1.
      + eexact EXEC.
    - seq_inversion.
      assert (EXEC1: c == s1 ==> c'0) by (eapply IHSTEP; eexact STEP1).
      eapply bs_Seq.
      + eexact EXEC1.
      + eexact STEP2.
    - eapply bs_If_True.
      + eexact SCVAL.
      + eexact EXEC.
    - eapply bs_If_False.
      + eexact SCVAL.
      + eexact EXEC.
    - inversion EXEC; subst.
      + seq_inversion.
        eapply bs_While_True.
        * eexact CVAL.
        * eexact STEP1.
        * eexact STEP2.
      + inversion STEP0; subst.
        eapply bs_While_False.
        eexact CVAL.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intro H.
    - induction H.
      + apply ss_int_Base. constructor.
      + apply ss_int_Base. constructor. assumption.
      + apply ss_int_Base. constructor.
      + apply ss_int_Base. constructor. assumption.
      + eapply ss_ss_composition.
        * eexact IHbs_int1.
        * eexact IHbs_int2.
      + eapply ss_int_Step.
        * eapply ss_If_True. eexact CVAL.
        * eexact IHbs_int.
      + eapply ss_int_Step.
        * eapply ss_If_False. eexact CVAL.
        * eexact IHbs_int.
      + eapply ss_int_Step.
        * eapply ss_While.
        eapply ss_int_Step.
        * eapply ss_If_True. eexact CVAL.
        * eapply ss_ss_composition.
          { eexact IHbs_int1. }
          { eexact IHbs_int2. }
      + eapply ss_int_Step.
        * eapply ss_While.
        eapply ss_int_Step.
        * eapply ss_If_False. eexact CVAL.
        * apply ss_int_Base. constructor.
    - induction H.
      + eapply ss_bs_base. eexact H.
      + eapply ss_bs_step.
        * eexact H.
        * eexact IHss_int.
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
    induction s; simpl.
    - reflexivity.
    - rewrite Renaming.re_rename_id by assumption.
      rewrite Renaming.re_rename_expr by assumption.
      reflexivity.
    - rewrite Renaming.re_rename_id by assumption.
      reflexivity.
    - rewrite Renaming.re_rename_expr by assumption.
      reflexivity.
    - rewrite IHs1, IHs2.
      reflexivity.
    - rewrite Renaming.re_rename_expr by assumption.
      rewrite IHs1, IHs2.
      reflexivity.
    - rewrite Renaming.re_rename_expr by assumption.
      rewrite IHs.
      reflexivity.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    extensionality id0; unfold update, Renaming.rename_state.
    destruct (id_eq_dec (Renaming.rename_id r x) id0);
    destruct (id_eq_dec x (Renaming.rename_id r' id0)); try congruence.
    - destruct (id_eq_dec x x); congruence.
    - rewrite e in n. rewrite Renaming.re_rename_id in n; congruence.
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct c as [[st i] o], c' as [[st' i'] o'].
    generalize dependent r; induction Hbs; intros r; simpl;
    try (rewrite rename_state_update_permute); eauto; try econstructor; eauto.
    - destruct c' as [[st'' i''] o'']; econstructor; eauto.
    - destruct c' as [[st'' i''] o'']; eapply bs_While_True; eauto.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    apply renaming_invariant_bs with (r := r') in Hbs.
    destruct c as [[st i] o], c' as [[st' i'] o'].
    simpl in Hbs.
    rewrite !Renaming.rename_state_inv with (Hinv := Hinv) in Hbs.
    rewrite re_rename with (r' := r) in Hbs; try assumption.
    assumption.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold sem_eq; intros c c'.
    split; intro Hbs.
    - apply renaming_invariant_bs with (r := r) in Hbs.
      assumption. 
    - eapply renaming_invariant_bs_inv; [eexact Hinv | eexact Hbs].
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
    
Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof.
  generalize dependent S.
  induction EXEC; intros S DEF.
  - simpl in DEF. inversion DEF.
  - simpl in DEF.
    destruct k eqn:K; subst; simpl in DEF; inversion DEF; subst.
    + inversion CSTEP; subst.
      constructor.
    + eapply IHEXEC. reflexivity.
  - simpl in DEF.
    destruct k eqn:K; subst; simpl in DEF; inversion DEF; subst.
    + inversion CSTEP; subst.
      econstructor; eexact CVAL.
    + eapply bs_Seq.
      * econstructor; eexact CVAL.
      * eapply IHEXEC. reflexivity.
  - simpl in DEF.
    destruct k eqn:K; subst; simpl in DEF; inversion DEF; subst.
    + inversion CSTEP; subst.
      constructor.
    + eapply bs_Seq.
      * constructor.
      * eapply IHEXEC. reflexivity.
  - simpl in DEF.
    destruct k eqn:K; subst; simpl in DEF; inversion DEF; subst.
    + inversion CSTEP; subst.
      econstructor; eexact CVAL.
    + eapply bs_Seq.
      * econstructor; eexact CVAL.
      * eapply IHEXEC. reflexivity.
  - simpl in DEF.
    eapply IHEXEC.
    destruct k; simpl; reflexivity.
  - simpl in DEF.
    destruct k eqn:K; subst; simpl in DEF; inversion DEF; subst.
    + eapply bs_If_True; [eexact CVAL |].
      eapply IHEXEC. reflexivity.
    + eapply bs_Seq.
      * eapply bs_If_True; [eexact CVAL |].
        eapply IHEXEC. reflexivity.
      * eapply IHEXEC. reflexivity.
  - simpl in DEF.
    destruct k eqn:K; subst; simpl in DEF; inversion DEF; subst.
    + eapply bs_If_False; [eexact CVAL |].
      eapply IHEXEC. reflexivity.
    + eapply bs_Seq.
      * eapply bs_If_False; [eexact CVAL |].
        eapply IHEXEC. reflexivity.
      * eapply IHEXEC. reflexivity.
  - simpl in DEF.
    destruct k eqn:K; subst; simpl in DEF; inversion DEF; subst.
    + assert (Hbody: c == s ;; WHILE e DO s END ==> c').
      { eapply IHEXEC. simpl. reflexivity. }
      inversion Hbody; subst.
      eapply bs_While_True; eauto.
    + assert (Hbody: c == s ;; WHILE e DO s END ;; s0 ==> c').
      { eapply IHEXEC. simpl. reflexivity. }
      inversion Hbody; subst.
      inversion STEP1; subst.
      eapply bs_Seq.
      * eapply bs_While_True; eauto.
      * eexact STEP2.
  - simpl in DEF.
    destruct k eqn:K; subst; simpl in DEF; inversion DEF; subst.
    + inversion CSTEP; subst.
      eapply bs_While_False; eexact CVAL.
    + eapply bs_Seq.
      * eapply bs_While_False; eexact CVAL.
      * eapply IHEXEC. reflexivity.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  eapply cps_bs_gen with (S1 := !s1) (k := !s2).
  - eexact STEP.
  - simpl.
    reflexivity.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
  eapply cps_bs_gen with (S1 := !s) (k := KEmpty).
  - eexact STEP.
  - simpl.
    reflexivity.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1 eqn:K1; destruct k2 eqn:K2; destruct k3 eqn:K3;
  simpl in *; auto.
  - eapply cps_Seq.
    simpl.
    eexact STEP.
  - eapply cps_Seq. simpl. eexact STEP.
  - eexact STEP.
  - eexact STEP.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  generalize dependent c3.
  generalize dependent k.
  induction EXEC; intros k c3 STEP.
  - eexact STEP.
  - eapply cps_Assign; [eexact CVAL |].
    inversion STEP; subst.
    eexact CSTEP.
  - eapply cps_Read.
    inversion STEP; subst; eexact CSTEP.
  - eapply cps_Write; [eexact CVAL |].
    inversion STEP; subst; eexact CSTEP.
  - eapply cps_Seq.
    eapply IHEXEC1.
    apply cps_cont_to_seq.
    simpl. eapply IHEXEC2. eexact STEP.
  - eapply cps_If_True; [eexact CVAL |].
    eapply IHEXEC; eexact STEP.
  - eapply cps_If_False; [eexact CVAL |].
    eapply IHEXEC; eexact STEP.
  - eapply cps_While_True; [eexact CVAL |].
    eapply IHEXEC1.
    apply cps_cont_to_seq. simpl.
    eapply IHEXEC2. eexact STEP.
  - eapply cps_While_False; [eexact CVAL |].
    inversion STEP; subst; eexact CSTEP.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont with (k := KEmpty).
  - eexact EXEC.
  - apply cps_Skip.
    apply cps_Empty.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
