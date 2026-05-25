Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

Require Import Stdlib.Program.Equality.

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
Proof. unfold contextual_equivalent in H. specialize H with Hole. simpl in H. apply H. Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. remember (Id 0) as i. exists (i ::= (Nat 0)). exists (i ::= (Nat 1)). split.
- unfold eval_equivalent. intros. split;
  intros; inversion H; inversion H0; subst; econstructor; constructor; constructor.
- intros Hyp. unfold contextual_equivalent in Hyp. specialize Hyp with (SeqL Hole (WRITE (Var i))).
  simpl in Hyp. unfold eval_equivalent in Hyp. specialize Hyp with ([]) ([0%Z]).
  assert (<|(i ::= (Nat 0));; (WRITE (Var i))|> [] => [0%Z]).
    { unfold eval. remember ([(i, 0%Z)]) as fs. exists fs.
      apply bs_Seq with (c' := (fs, [], [])).
      { replace fs with ([] [i <- 0%Z]).
        apply bs_Assign. auto. }
      { apply bs_Write. constructor. rewrite Heqfs. constructor. } }
  assert (~(eval ((i ::= Nat 1);; WRITE (Var i)) ([]) ([0%Z]))).
    { intros Hyp0. inversion Hyp0. inversion H0. subst. inversion STEP1. subst.
      inversion VAL. subst. inversion STEP2. inversion VAL0. subst. inversion VAR. congruence. }
  tauto.
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
  Proof. unfold bs_equivalent. intros. split;
  intros; seq_inversion; seq_inversion; seq_apply.
  Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. unfold bs_equivalent. split.
  - intros. inversion_clear H.
    + constructor.
      * apply CVAL.
      * econstructor.
        { apply STEP. }
        { apply WSTEP. }
    + apply bs_If_False.
      * apply CVAL.
      * auto.
  - intros. inversion H.
    + inversion STEP. subst. econstructor.
      * apply CVAL.
      * eauto.
      * apply STEP2.
    + subst. inversion STEP. apply bs_While_False. apply CVAL.
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof. dependent induction EXE.
  - apply (IHEXE2 e s st i o).
    + reflexivity.
    + reflexivity.
  - apply CVAL.
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. unfold bs_equivalent. intros. split.
  - intros. remember (Nat 1) as e1. destruct c' as [[st i] o].
    apply (while_false e1 SKIP st i o c) in H. subst. inversion H.
  - intros. inversion H; inversion CVAL.
  Qed.

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof. unfold bs_equivalent. intros. split; intros.
  - dependent induction H.
    + subst. eapply bs_While_True.
      * apply CVAL.
      * apply EQ. apply H.
      * apply (IHbs_int2 _ s1).
        { apply EQ. }
        { reflexivity. }
    + auto.
  - dependent induction H.
    + subst. eapply bs_While_True.
      * apply CVAL.
      * apply EQ. apply H.
      * apply (IHbs_int2 _ s2).
        { apply EQ. }
        { reflexivity. }
    + auto.
  Qed.

  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. intros H. remember (Nat 1) as e1. destruct c' as [[st i] o].
  apply (while_false e1 s st i o) in H. subst. inversion H.
  Qed.

End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof. unfold bs_equivalent. intros. split; intros;
seq_inversion; apply EQ in STEP2; seq_apply.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof. unfold bs_equivalent. intros. split; intros;
seq_inversion; apply EQ in STEP1; seq_apply.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. unfold bs_equivalent. intros. split; intros;
inversion H; subst;
(constructor) + (apply EQ in STEP; apply bs_If_False);
(apply CVAL) + (apply STEP).
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. unfold bs_equivalent. intros. split; intros;
inversion H; subst;
(apply bs_If_True; apply EQ in STEP) + apply bs_If_False;
apply CVAL + apply STEP.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. unfold bs_equivalent. intros. split; intros;
dependent induction H.
- apply EQ in H. apply (bs_While_True _ _ _ c' c'');
  try apply (IHbs_int2 e s1); auto.
- apply bs_While_False. auto.
- apply EQ in H. apply (bs_While_True _ _ _ c' c'');
  try apply (IHbs_int2 e s2); auto.
- apply bs_While_False. auto.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof. split.
- apply eq_congruence_seq_r. auto.
- split.
  + apply eq_congruence_seq_l. auto.
  + split.
    * apply eq_congruence_cond_else. auto.
    * split.
      { apply eq_congruence_cond_then. auto. }
      { apply eq_congruence_while. auto. }
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
Proof. generalize dependent c2. dependent induction EXEC1; intros.
- inversion_clear EXEC2. reflexivity.
- inversion_clear EXEC2. by_eval_deterministic.
- inversion_clear EXEC2. reflexivity.
- inversion_clear EXEC2. by_eval_deterministic.
- inversion EXEC2. subst.
  assert (c' = c'0). { apply IHEXEC1_1. auto. } subst c'0.
  apply IHEXEC1_2. auto.
- inversion_clear EXEC2.
  + apply IHEXEC1. apply STEP.
  + eval_zero_not_one.
- inversion_clear EXEC2.
  + eval_zero_not_one.
  + apply IHEXEC1. apply STEP.
- inversion EXEC2. subst.
  + assert (c' = c'0). { apply IHEXEC1_1. auto. } subst c'0.
    apply IHEXEC1_2. auto.
  + subst. eval_zero_not_one.
- inversion_clear EXEC2.
  + eval_zero_not_one.
  + reflexivity.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma update_equiv (st1 st2: state Z) (i: id) (z: Z) (EQ: equivalent_states st1 st2):
  equivalent_states (st1 [i <- z]) (st2 [i <- z]).
Proof. unfold equivalent_states. intros. destruct (id_eq_dec i id).
- unfold Expr.equivalent_states. intros z0. subst. split;
  intros; apply update_eq' in H; subst; apply update_eq.
- unfold Expr.equivalent_states. intros z0. split;
  intros; apply update_neq; auto; apply update_neq in H; auto; apply EQ; auto.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
generalize dependent i. generalize dependent i'. generalize dependent o. generalize dependent o'.
generalize dependent st1. generalize dependent st2. generalize dependent st1'.
induction s; intros.
(* inversion H; subst. *)
- inversion H; subst. exists st1'. auto.
- inversion H; subst. exists (st1' [i <- z]). split.
  + apply update_equiv. auto.
  + constructor. apply variable_relevance with (s1 := st1); auto.
- inversion H; subst. exists (st1' [i <- z]). split.
  + apply update_equiv. auto.
  + auto.
- inversion H; subst. exists st1'. split.
  + auto.
  + constructor. apply variable_relevance with (s1 := st2); auto.
- inversion H; subst. destruct c' as [[stm im] om].
  apply IHs1 with (st1' := st1') in STEP1; auto. destruct STEP1 as [stm' [EQM' EVALM']].
  apply IHs2 with (st1' := stm') in STEP2; auto. destruct STEP2 as [st2' [EQ2' EVAL2']].
  exists st2'. split.
  + auto.
  + apply bs_Seq with (c' := (stm', im, om)); auto.
- inversion H; subst.
  + apply IHs1 with (st1' := st1') in STEP; auto. destruct STEP as [st2' [EQ2' EVAL2']].
    exists st2'. split.
    * auto.
    * apply bs_If_True.
      -- apply variable_relevance with (s1 := st1); auto.
      -- auto.
  + apply IHs2 with (st1' := st1') in STEP; auto. destruct STEP as [st2' [EQ2' EVAL2']].
    exists st2'. split.
    * auto.
    * apply bs_If_False.
      -- apply variable_relevance with (s1 := st1); auto.
      -- auto.
- dependent induction H.
  + apply IHbs_int1 with (st1 := st1); auto.
    (* Maybe a properly stated auxillary lemma (bs_equiv_while_true_step or something) would help *)
    * admit.
    * admit.
  + exists st1'. split.
    * auto.
    * apply bs_While_False. apply variable_relevance with (s1 := st2); auto.
Admitted.

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
  Proof. generalize dependent c''. dependent induction EXEC1; intros; inversion EXEC2; subst;
  try reflexivity.
  - by_eval_deterministic.
  - by_eval_deterministic.
  - assert ((@None stmt, c') = (@None stmt, c'0)). { apply IHEXEC1. auto. }
    f_equal. inversion H. reflexivity.
  - assert ((@None stmt, c') = (Some s1', c'0)). { apply IHEXEC1. auto. }
    inversion H.
  - apply IHEXEC1 in SSTEP. congruence.
  - apply IHEXEC1 in SSTEP. inversion SSTEP. reflexivity.
  - eval_zero_not_one.
  - eval_zero_not_one.
  Qed.

  Ltac by_ss_int_step_deterministic :=
  match goal with
    H1: ?c --?s--> ?c1, H2: ?c --?s--> ?c2 |- _ =>
     apply (ss_int_step_deterministic s c c1 c2) in H1; [subst c2; reflexivity | assumption]
  end.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof. dependent induction STEP1.
  - dependent induction STEP2.
    + remember (None, c') as ct'. remember (None, c'0) as ct'0. assert (ct' = ct'0).
        { by_ss_int_step_deterministic. }
      congruence.
    + remember (None, c') as ct'. remember (Some s', c'0) as ct'0.
      assert (ct' = ct'0). { by_ss_int_step_deterministic. }
      congruence.
  - dependent induction STEP2.
    + remember (Some s', c') as ct'. remember (None, c'0) as ct'0.
      assert (ct' = ct'0). { by_ss_int_step_deterministic. }
      congruence.
    + remember (Some s', c') as ct'. remember (Some s'0, c'0) as ct'0.
      assert (ct' = ct'0). { by_ss_int_step_deterministic. }
      subst. inversion H1. subst. apply IHSTEP1. apply STEP2.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. inversion_clear STEP; try constructor; apply SVAL; auto.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof. dependent induction STEP1.
  - assert (c --s;; s2--> (Some s2, c'0)).
      { apply ss_Seq_Compl. apply H. }
    apply (ss_int_Step (s;; s2) s2 c c'0 c').
    + apply H0.
    + apply STEP2.
  - apply (ss_int_Step (s;; s2) (s';; s2) c c'0 c').
    + apply (ss_Seq_InCompl c c'0 s s2 s'). apply H.
    + apply IHSTEP1. apply STEP2.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof. generalize dependent c. generalize dependent c'. generalize dependent c''. generalize dependent s'.
  induction s.
  - intros. inversion STEP.
  - intros. inversion STEP.
  - intros. inversion STEP.
  - intros. inversion STEP.
  - intros. inversion STEP.
    + subst. apply (bs_Seq c c' c'').
      * apply ss_bs_base. apply SSTEP.
      * apply EXEC.
    + subst. inversion EXEC. subst.
      apply IHs1 with (c := c) in STEP1 as SEVAL1; auto.
      apply bs_Seq with (c' := c'0); auto.
  - intros. inversion STEP.
    (* `constructor` is not smart enough *)
    + subst. apply bs_If_True; auto.
    + subst. apply bs_If_False; auto.
  - intros. apply SmokeTest.while_unfolds. inversion STEP. subst. apply EXEC.
  Qed.

  Lemma ss_while_false (st: state Z) (i o: list Z) (s: stmt) (e: expr)
        (FALSE: [|e|] st => Z.zero):
    (st, i, o) --WHILE e DO s END-->> (st, i, o).
  Proof.
  apply (ss_int_Step (WHILE e DO s END)
         (COND e THEN s ;; WHILE e DO s END ELSE SKIP END)
         (st, i, o) (st, i, o)).
  - constructor.
  - apply (ss_int_Step _ SKIP _ (st, i, o)).
    + constructor. auto.
    + constructor. constructor.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. split; intros.
  - dependent induction H.
    + constructor. constructor.
    + constructor. constructor. auto.
    + constructor. constructor.
    + constructor. constructor. auto.
    + apply (ss_ss_composition c c'' c'); auto.
    + apply (ss_int_Step (COND e THEN s1 ELSE s2 END) s1 (s, i, o) (s, i, o)).
      * constructor. auto.
      * auto.
    + apply (ss_int_Step (COND e THEN s1 ELSE s2 END) s2 (s, i, o) (s, i, o)).
      * constructor. auto.
      * auto.
    + apply ss_int_Step with (s' := (COND e THEN (s ;; WHILE e DO s END) ELSE SKIP END)) (c' := (st, i, o)).
      * apply ss_While.
      * assert ((st, i, o) --s;; WHILE e DO s END-->> c'').
          { apply (ss_ss_composition (st, i, o) c'' c' s (WHILE e DO s END)); auto. }
        apply ss_int_Step with (s' := s;; WHILE e DO s END) (c' := (st, i, o)).
        -- apply ss_If_True. auto.
        -- auto.
    + apply ss_while_false. auto.
  - dependent induction H.
    + apply ss_bs_base. auto.
    + apply (ss_bs_step c c' c'' s s'); auto.
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
  - constructor.
  - unfold rename. f_equal.
    + auto.
    + apply Renaming.re_rename_expr. auto.
  - unfold rename. f_equal. auto.
  - unfold rename. f_equal. apply Renaming.re_rename_expr. auto.
  - simpl. rewrite IHs1. rewrite IHs2. reflexivity.
  - simpl. rewrite IHs1. rewrite IHs2. f_equal. apply Renaming.re_rename_expr. auto.
  - simpl. rewrite IHs. f_equal. apply Renaming.re_rename_expr. auto.
  Qed.

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. destruct st.
  - replace [][x <- z] with [(x, z)] by auto.
    rewrite Renaming.rename_state_id. auto.
  - unfold update. rewrite Renaming.rename_state_dist_unary. simpl. reflexivity.
  Qed.

  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof. dependent induction Hbs.
  - simpl. constructor.
  - unfold rename_conf. rewrite rename_state_update_permute. simpl. constructor.
    apply Renaming.eval_renaming_invariance. auto.
  - unfold rename_conf. rewrite rename_state_update_permute. simpl. constructor.
  - unfold rename_conf. constructor. apply Renaming.eval_renaming_invariance. auto.
  - simpl. apply (bs_Seq _ (rename_conf r c') _); auto.
  - simpl. econstructor.
    (* Somehow this doesn't work:
    + auto using Renaming.eval_renaming_invariance. *)
    + apply Renaming.eval_renaming_invariance. auto.
    + auto.
  - simpl. apply bs_If_False.
    + apply Renaming.eval_renaming_invariance. auto.
    + auto.
  - simpl. apply (bs_While_True _ _ _ (rename_conf r c') _).
    + apply Renaming.eval_renaming_invariance. auto.
    + auto.
    + auto.
  - simpl. apply bs_While_False. apply Renaming.eval_renaming_invariance. auto.
  Qed.

  (* Inverse order of renamings in INV saves a few steps here *)
  Lemma re_rename_conf (r r': renaming) (c: conf) (INV: Renaming.renamings_inv r' r):
    rename_conf r' (rename_conf r c) = c.
  Proof. destruct c as [[st i] o]. unfold rename_conf. repeat f_equal. apply Renaming.re_rename_state.
  apply INV. Qed.

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof. pose proof Renaming.renaming_inv. specialize H with r. destruct H as [r' RINV].
  replace (c ==s==> c') with
    ((rename_conf r' (rename_conf r c)) ==(rename r' (rename r s))==> (rename_conf r' (rename_conf r c'))).
  - apply renaming_invariant_bs. apply Hbs.
  - rewrite re_rename by auto. f_equal.
    + apply re_rename_conf. apply RINV.
    + apply re_rename_conf. apply RINV.
  Qed.

  Lemma renaming_inv_comm (r r': renaming):
    Renaming.renamings_inv r r' <-> Renaming.renamings_inv r' r.
  Proof. unfold Renaming.renamings_inv. destruct r as [f]. destruct r' as [f']. simpl. split; intros.
  - assert (FinFun.Injective f). { auto using Renaming.bijective_injective. }
    unfold FinFun.Injective in H0. assert (f (f' (f x)) = f x) by auto. auto.
  - assert (FinFun.Injective f'). { auto using Renaming.bijective_injective. }
    unfold FinFun.Injective in H0. assert (f' (f (f' x)) = f' x) by auto. auto.
  Qed.

  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof. unfold eval_equivalent. unfold eval. intros. split; intros.
  - destruct H as [st]. exists (Renaming.rename_state r st).
    assert (([], i, []) = rename_conf r ([], i, [])).
      { reflexivity. }
    assert ((Renaming.rename_state r st, [], o) = rename_conf r (st, [], o)).
      { reflexivity. }
    rewrite H0. rewrite H1. apply renaming_invariant_bs. apply H.
  - destruct H as [st].
    pose proof Renaming.renaming_inv. specialize H0 with r. destruct H0 as [r' RINV].
    exists (Renaming.rename_state r' st).
    assert (([], i, []) = rename_conf r ([], i, [])) by reflexivity.
    assert ((st, [], o) = rename_conf r (Renaming.rename_state r' st, [], o)).
      { simpl. repeat f_equal. symmetry. apply Renaming.re_rename_state.
        rewrite renaming_inv_comm. apply RINV. }
    rewrite H0 in H. rewrite H1 in H. apply (renaming_invariant_bs_inv _ r).
    apply H.
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

(* Step from k to S. H is the cps definition of S, HH is the bs constructor *)
Ltac cps_bs_gen_helper k H HH :=
  destruct k eqn:K; subst; inversion H; subst;
  [inversion EXEC; subst | eapply bs_Seq; eauto];
  apply HH; auto.

Lemma bs_while_true_folds (st: state Z) (i o: list Z) (c': conf) (s: stmt) (e: expr)
        (SEQ: (st, i, o) ==s;; WHILE e DO s END==> c')
        (TRUE: [|e|] st => Z.one):
  (st, i, o) ==WHILE e DO s END==> c'.
Proof. inversion SEQ. subst. apply bs_While_True with (c' := c'0); auto. Qed.

Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof. generalize dependent S.
induction EXEC; intros.
- inversion DEF.
- cps_bs_gen_helper k DEF bs_Skip.
- cps_bs_gen_helper k DEF bs_Assign.
- cps_bs_gen_helper k DEF bs_Read.
- cps_bs_gen_helper k DEF bs_Write.
- destruct k eqn:K; subst; inversion DEF; subst.
  + apply IHEXEC. eauto.
  + apply SmokeTest.seq_assoc. apply IHEXEC. constructor.
- destruct k eqn:K; subst; inversion DEF; subst.
  + apply bs_If_True; auto.
  + assert (s, i, o) ==s1;; s0==> c'.
      { apply IHEXEC. auto. }
    inversion H. subst.
    apply bs_Seq with (c' := c'0); auto.
- destruct k eqn:K; subst; inversion DEF; subst.
  + apply bs_If_False; auto.
  + assert (s, i, o) ==s2;; s0==> c'.
      { apply IHEXEC. auto. }
    inversion H. subst.
    apply bs_Seq with (c' := c'0); auto.
- destruct k eqn:K; subst; inversion DEF; subst.
  + apply SmokeTest.while_unfolds. auto.
  + assert ((st, i, o) ==(s;; WHILE e DO s END;; s0)==> c').
      { apply IHEXEC. auto. }
    apply SmokeTest.seq_assoc in H. inversion H. subst. apply bs_Seq with (c' := c'0).
    * apply bs_while_true_folds; auto.
    * auto.
- destruct k eqn:K; subst; inversion DEF; subst.
  + inversion EXEC. subst. apply bs_While_False. auto.
  + assert ((st, i, o) ==s0==> c') by auto.
    eapply bs_Seq; auto.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. eapply cps_bs_gen; eauto. Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. eapply cps_bs_gen; eauto. Qed.

Lemma empty_app (st1 st2: cont) (KEMPTY: st1 @ st2 = KEmpty):
  st1 = KEmpty /\ st2 = KEmpty.
Proof. split;
  unfold Kapp in KEMPTY; destruct st2;
  destruct st1; auto; discriminate.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. destruct k1.
- inversion STEP. subst. replace (KEmpty @ k2) with k2 by auto.
  symmetry in H0. apply empty_app in H0. destruct H0. subst. auto.
- destruct k2.
  + apply STEP.
  + apply cps_Seq. apply STEP.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. generalize dependent k. generalize dependent c3.
dependent induction EXEC; intros; subst.
- auto.
- inversion STEP. eapply cps_Assign; eauto.
- inversion STEP. eapply cps_Read; auto.
- inversion STEP. eapply cps_Write; eauto.
- replace (!(s1;; s2)) with ((KStmt s1) @ (KStmt s2)) by auto.
  apply cps_cont_to_seq. apply IHEXEC1. apply cps_Skip. destruct k.
  + auto.
  + apply cps_Seq. replace (!s @ KEmpty) with (!s) by auto.
    apply IHEXEC2. apply STEP.
- apply cps_If_True; auto.
- apply cps_If_False; auto.
- apply cps_While_True; auto. destruct k; apply IHEXEC1; apply cps_Skip.
  + replace (!(WHILE e DO s END) @ KEmpty) with (!(WHILE e DO s END)) by auto.
    apply IHEXEC2. apply STEP.
  + replace (!(WHILE e DO s END) @ !s0) with !(WHILE e DO s END;; s0) by auto.
    apply cps_Seq. apply IHEXEC2. apply STEP.
- inversion STEP. apply cps_While_False; auto.
Qed.

Lemma cps_int_trans (c1 c2 c3: conf) (s1 s2: stmt)
      (STEP1: KEmpty |- c1 --!s1--> c2) (STEP2: KEmpty |- c2 --!s2--> c3):
  KEmpty |- c1 --!s1 @ !s2--> c3.
Proof. apply cps_Seq. apply cps_int_to_bs_int in STEP1. apply bs_int_to_cps_int_cont with (c2 := c2).
- auto.
- constructor. auto.
Qed.

Lemma empty_skip (c: conf):
  KEmpty |- c --!SKIP--> c.
Proof. repeat constructor. Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. dependent induction EXEC.
- constructor. constructor.
- repeat econstructor; eauto.
- repeat econstructor; eauto.
- repeat econstructor; eauto.
- (* We have very strange induction hypotheses at this point, but still can prove the rigth ones by ourselves *)
  (* But that doesn't mean induction is redundant... *)
  assert (KEmpty |- c' --!s2--> c'') as IH1.
    { specialize empty_skip with c'' as ESKIP.
      apply bs_int_to_cps_int_cont with (c2 := c''); auto. }
  assert (KEmpty |- (st, i, o) --!s1--> c') as IH2.
    { specialize empty_skip with c' as ESKIP.
      apply bs_int_to_cps_int_cont with (c2 := c'); auto. }
  replace !(s1;; s2) with !s1 @ !s2 by auto.
  apply cps_int_trans with (c2 := c'); auto.
- (* Induction is nneded here *) apply cps_If_True; auto.
- apply cps_If_False; auto.
- (* Again, very strange induction hypotheses *)
  assert (KEmpty |- (st, i, o) --!s--> c') by auto.
  assert (KEmpty |- c' --!(WHILE e DO s END)--> c'').
    { specialize empty_skip with c'' as ESKIP.
      apply bs_int_to_cps_int_cont with (c2 := c''); auto. }
  apply cps_While_True; auto.
  assert (KEmpty |- (st, i, o) --!s @ !(WHILE e DO s END)--> c'').
    { apply cps_int_trans with (c2 := c'); auto. }
  replace !s @ !(WHILE e DO s END) with !(s;; WHILE e DO s END) in H1 by auto.
  inversion H1. subst. apply CSTEP.
- apply cps_While_False; auto. constructor.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
