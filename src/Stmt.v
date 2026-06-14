Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

From hahn Require Import HahnBase.

Require Import Stdlib.Program.Equality.

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
  apply (H Hole).
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists SKIP, (Id 0 ::= Nat 1).
  split.
  - intros i o. split; intros [st H]; inversion H; subst.
    + exists ([][ Id 0 <- Z.one]).
      constructor. constructor.
    + exists []. constructor.
  - intros Hc.
      set (C := SeqL Hole (WRITE (Var (Id 0)))).
      assert (Hpos : <| C <~ (Id 0 ::= Nat 1) |> [] => [Z.one]).
      { unfold C. simpl. unfold eval.
        eexists. eapply bs_Seq.
        - eapply bs_Assign. constructor.
        - eapply bs_Write. constructor.
          apply update_eq. }
      assert (Hneg : ~ <| C <~ SKIP |> [] => [Z.one]).
      { unfold C. simpl. unfold eval.
        intros [st H].
        inversion H; subst.
        inversion STEP1; subst.
        inversion STEP2; subst.
        inversion VAL; subst.
        inversion VAR. }
      apply Hneg.
      apply (Hc C).
      apply Hpos.
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
    split; intro H;
    seq_inversion;
    seq_inversion;
    eapply bs_Seq.
    - eassumption.
    - eapply bs_Seq; eassumption.
    - eapply bs_Seq; eassumption.
    - eassumption.
  Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    split; intro; inversion H; subst.
    - apply bs_If_True.
      + assumption.
      + eapply bs_Seq; eassumption.
    - apply bs_If_False.
      + assumption.
      + constructor.
    - seq_inversion.
      eapply bs_While_True; eassumption.
    - inversion STEP; subst.
      apply bs_While_False. assumption.
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END).
    remember (st, i, o).
    induction EXE; inversion Heqs0; subst.
    - apply IHEXE2; reflexivity.
    - inversion Heqp; subst.
      assumption.
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    intros. split; intro.
    - exfalso.
      remember (WHILE (Nat 1) DO SKIP END) as Hloop.
      induction H; inversion HeqHloop; subst.
      + apply IHbs_int2. reflexivity.
      + inversion CVAL.
    - exfalso.
      inversion H; subst; inversion CVAL.
  Qed.

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    intros. split; intro.
    - remember (WHILE e DO s1 END) as Hloop.
      induction H; inversion HeqHloop; subst.
      + eapply bs_While_True.
        * assumption.
        * apply EQ. eassumption.
        * apply IHbs_int2. reflexivity.
      + apply bs_While_False. assumption.
    - remember (WHILE e DO s2 END) as Hloop.
      induction H; inversion HeqHloop; subst.
      + eapply bs_While_True.
        * assumption.
        * apply EQ. eassumption.
        * apply IHbs_int2. reflexivity.
      + apply bs_While_False. assumption.
  Qed.

  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro.
    remember (WHILE (Nat 1) DO s END) as Hloop.
    induction H; inversion HeqHloop; subst.
    - apply IHbs_int2. reflexivity.
    - inversion CVAL.
  Qed.

End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  split; intro;
  seq_inversion;
  eapply bs_Seq;
  eassumption || (apply EQ; eassumption).
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  split; intro;
  seq_inversion;
  eapply bs_Seq;
  eassumption || (apply EQ; eassumption).
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  split; intro;
  inversion H; subst.
  - apply bs_If_True; eassumption.
  - apply bs_If_False.
    + eassumption.
    + apply EQ. eassumption.
  - apply bs_If_True; eassumption.
  - apply bs_If_False.
    + eassumption.
    + apply EQ. eassumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  split; intro;
  inversion H; subst.
  - apply bs_If_True.
    + eassumption.
    + apply EQ. eassumption.
  - apply bs_If_False; eassumption.
  - apply bs_If_True.
    + eassumption.
    + apply EQ. eassumption.
  - apply bs_If_False; eassumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  split; intro.
  - remember (WHILE e DO s1 END) as Hloop.
    induction H; inversion HeqHloop; subst.
    + eapply bs_While_True.
      * assumption.
      * apply EQ. eassumption.
      * apply IHbs_int2. reflexivity.
    + apply bs_While_False. eassumption.
  - remember (WHILE e DO s2 END) as Hloop.
    induction H; inversion HeqHloop; subst.
    + eapply bs_While_True.
      * assumption.
      * apply EQ. eassumption.
      * apply IHbs_int2. reflexivity.
    + apply bs_While_False. eassumption.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. apply eq_congruence_seq_r. assumption.
  split. apply eq_congruence_seq_l. assumption.
  split. apply eq_congruence_cond_else. assumption.
  split. apply eq_congruence_cond_then. assumption.
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
  generalize dependent c2.
  induction EXEC1; intros;
  inversion EXEC2; subst.
  - reflexivity.
  - apply (eval_deterministic e s z z0 VAL) in VAL0. subst. reflexivity.
  - reflexivity.
  - apply (eval_deterministic e s z z0 VAL) in VAL0. subst. reflexivity.
  - apply IHEXEC1_2. specialize (IHEXEC1_1 c'0 STEP1). subst. assumption.
  - apply IHEXEC1. assumption.
  - eval_zero_not_one.
  - eval_zero_not_one.
  - apply IHEXEC1. assumption.
  - specialize (IHEXEC1_1 c'0 STEP). subst. auto.
  - eval_zero_not_one.
  - eval_zero_not_one.
  - reflexivity.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')  
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  generalize dependent st1'.
  dependent induction H; intros.
  - (* SKIP *)
    exists st1'. auto.
  - (* Assign *)
    exists (st1' [x <- z]). split.
    + intro. unfold Expr.equivalent_states. intro.
      destruct (id_eq_dec id x); subst.
      * split; intro Hb; inversion Hb; subst.
        -- constructor.
        -- contradiction.
        -- constructor.
        -- contradiction.
      * split; intro Hb;
        rewrite <- update_neq.
        -- apply HE1.
           rewrite <- update_neq in Hb. apply Hb.
           symmetry. apply n.
        -- symmetry. apply n.
        -- apply HE1.
           rewrite <- update_neq in Hb. apply Hb.
           symmetry. apply n.
        -- symmetry. apply n.
    + constructor.
      eapply variable_relevance; auto.
  - (* Read *)
    exists (st1' [x <- z]). split.
    + intro id. unfold Expr.equivalent_states. intro z0.
      destruct (id_eq_dec id x); subst.
      * split; intro Hb; inversion Hb; subst.
        -- constructor.
        -- contradiction.
        -- constructor.
        -- contradiction.
      * split; intro Hb;
        rewrite <- update_neq.
        -- apply HE1.
           rewrite <- update_neq in Hb. apply Hb.
           symmetry. apply n.
        -- symmetry. apply n.
        -- apply HE1.
           rewrite <- update_neq in Hb. apply Hb.
           symmetry. apply n.
        -- symmetry. apply n.
    + constructor.
  - (* Write *)
    exists st1'. split.
    + assumption.
    + constructor.
      eapply variable_relevance; auto.
  - (* Seq *)
    destruct c' as [[st4 i4] o4].
    specialize (IHbs_int1 i o i4 o4 st1 st4 JMeq_refl JMeq_refl st1' HE1).
    destruct IHbs_int1 as [st4' [HE4 STEP1']].
    specialize (IHbs_int2 i4 o4 i' o' st4 st2 JMeq_refl JMeq_refl st4' HE4).
    destruct IHbs_int2 as [st2' [HE2 STEP2']].
    exists st2'. split.
    + assumption.
    + econstructor; eassumption.
  - (* If_True *)
    specialize (IHbs_int i o i' o' st1 st2 JMeq_refl JMeq_refl st1' HE1).
    destruct IHbs_int as [st2' [HE2 STEP']].
    exists st2'. split.
    + assumption.
    + apply bs_If_True.
      * eapply variable_relevance; auto.
      * assumption.
  - (* If_False *)
    specialize (IHbs_int i o i' o' st1 st2 JMeq_refl JMeq_refl st1' HE1).
    destruct IHbs_int as [st2' [HE2 STEP']].
    exists st2'. split.
    + assumption.
    + apply bs_If_False.
      * eapply variable_relevance; auto.
      * assumption.
  - (* While_True *)
    destruct c' as [[st4 i4] o4].
    specialize (IHbs_int1 i o i4 o4 st1 st4 JMeq_refl JMeq_refl st1' HE1).
    destruct IHbs_int1 as [st4' [HE4 STEP1']].
    specialize (IHbs_int2 i4 o4 i' o' st4 st2 JMeq_refl JMeq_refl st4' HE4).
    destruct IHbs_int2 as [st2' [HE2 STEP2']].
    exists st2'. split.
    + assumption.
    + eapply bs_While_True.
      * eapply variable_relevance; auto.
      * eassumption.
      * assumption.
  - (* While_False *)
    exists st1'. split.
    + assumption.
    + apply bs_While_False.
      eapply variable_relevance; auto.
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
    generalize dependent c''. induction EXEC1; intros; inversion EXEC2; subst;
    try reflexivity; try by_eval_deterministic.
    - specialize (IHEXEC1 (None, c'0) SSTEP). inversion_clear IHEXEC1. reflexivity.
    - specialize (IHEXEC1 (Some s1', c'0) SSTEP). inversion IHEXEC1.
    - specialize (IHEXEC1 (None, c'0) SSTEP). inversion IHEXEC1.
    - specialize (IHEXEC1 (Some s1'0, c'0) SSTEP). inversion IHEXEC1. subst. reflexivity.
    - apply (eval_deterministic e s Z.one Z.zero SCVAL) in SCVAL0. inversion SCVAL0.
    - apply (eval_deterministic e s Z.zero Z.one SCVAL) in SCVAL0. inversion SCVAL0.
  Qed.

    Ltac by_step_deterministic :=
  match goal with
    | H1 : ?c -- ?s --> ?c',
      H2 : ?c -- ?s --> ?c'' |- _ =>
        apply (ss_int_step_deterministic s c c' c'' H1) in H2;
        inversion H2; subst; try reflexivity
  end.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''. induction STEP1; intros; inversion STEP2; subst.
    - by_step_deterministic.
    - apply (ss_int_step_deterministic s c (None, c') (Some s', c'0) H) in H0.
      inversion_clear H0.
    - apply (ss_int_step_deterministic s c (Some s', c') (None, c''0) H) in H0.
      inversion_clear H0.
    - apply (ss_int_step_deterministic s c (Some s', c') (Some s'0, c'0) H) in H0.
      inversion H0. subst. auto.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP; subst.
    - constructor.
    - constructor. assumption.
    - constructor.
    - constructor. assumption.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    induction STEP1;
    eapply ss_int_Step.
    - apply ss_Seq_Compl. eassumption.
    - eassumption.
    - apply ss_Seq_InCompl. eassumption.
    - apply IHSTEP1. assumption.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent c''.
    dependent induction STEP; intros c'' EXEC.
    - eapply bs_Seq.
      + eapply ss_bs_base. eassumption.
      + assumption.
    - seq_inversion.
      eapply bs_Seq.
      + eapply IHSTEP.
        * reflexivity.
        * eassumption.
      + assumption.
    - apply bs_If_True; assumption.
    - apply bs_If_False; assumption.
    - inversion EXEC; inversion STEP; subst;
      eauto.
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
      + eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step.
        * apply ss_If_True. assumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_If_False. assumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_True. assumption.
          -- eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_False. assumption.
          -- apply ss_int_Base. constructor.
    - induction H.
      + apply ss_bs_base. assumption.
      + eapply ss_bs_step.
        * eassumption.
        * assumption.
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
    - rewrite Hinv.
      rewrite (Renaming.re_rename_expr r r' Hinv).
      reflexivity.
    - rewrite Hinv.
      reflexivity.
    - rewrite (Renaming.re_rename_expr r r' Hinv).
      reflexivity.
    - rewrite IHs1, IHs2.
      reflexivity.
    - rewrite (Renaming.re_rename_expr r r' Hinv).
      rewrite IHs1, IHs2.
      reflexivity.
    - rewrite (Renaming.re_rename_expr r r' Hinv).
      rewrite IHs.
      reflexivity.
  Qed.

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    destruct r. reflexivity.
  Qed.

  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r as [f Hbij].
      induction Hbs; simpl.
      - constructor.
      - constructor.
        apply -> Renaming.eval_renaming_invariance. assumption.
      - constructor.
      - constructor.
        apply -> Renaming.eval_renaming_invariance. assumption.
      - eapply bs_Seq.
        + apply IHHbs1.
        + apply IHHbs2.
      - apply bs_If_True.
        + apply -> Renaming.eval_renaming_invariance. assumption.
        + apply IHHbs.
      - apply bs_If_False.
        + apply -> Renaming.eval_renaming_invariance. assumption.
        + apply IHHbs.
      - eapply bs_While_True.
        + apply -> Renaming.eval_renaming_invariance. assumption.
        + apply IHHbs1.
        + apply IHHbs2.
      - apply bs_While_False.
        apply -> Renaming.eval_renaming_invariance. assumption.
    Qed.

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r) as [r' Hinv].
    apply renaming_invariant_bs with (r := r') in Hbs.
    unfold rename_conf in Hbs.
    destruct c as [[st i] o]; destruct c' as [[st' i'] o'].
    simpl in Hbs.
    rewrite (Renaming.re_rename_state r' r Hinv) in Hbs.
    rewrite (Renaming.re_rename_state r' r Hinv) in Hbs.
    rewrite (re_rename r' r Hinv) in Hbs.
    assumption.
  Qed.

  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent.
    intros. split.
    - intros [st Hbs].
      apply renaming_invariant_bs with (r := r) in Hbs.
      simpl in Hbs.
      exists (Renaming.rename_state r st).
      exact Hbs.
    - intros [st Hbs].
      destruct (Renaming.renaming_inv2 r) as [r' Hinv].
      exists (Renaming.rename_state r' st).
      apply renaming_invariant_bs_inv with (r := r). simpl.
      rewrite (Renaming.re_rename_state r r' Hinv).
      exact Hbs.
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
  induction EXEC; intros S DEF; simpl in DEF.
  - inversion DEF.
  - cps_bs_gen_helper k DEF bs_Skip.
  - cps_bs_gen_helper k DEF bs_Assign.
  - cps_bs_gen_helper k DEF bs_Read.
  - cps_bs_gen_helper k DEF bs_Write.
  - destruct k; inversion DEF; subst;
    [ | apply SmokeTest.seq_assoc]; apply IHEXEC; simpl; reflexivity.
  - destruct k; inversion DEF; subst.
    + apply bs_If_True; auto.
    + assert (H := IHEXEC _ (ltac:(simpl; reflexivity))).
      seq_inversion. eapply bs_Seq; [eapply bs_If_True; eassumption | assumption].
  - destruct k; inversion DEF; subst.
    + apply bs_If_False; auto.
    + assert (H := IHEXEC _ (ltac:(simpl; reflexivity))).
      seq_inversion. eapply bs_Seq; [eapply bs_If_False; eassumption | assumption].
  - destruct k; inversion DEF; subst.
    + assert (H := IHEXEC _ (ltac:(simpl; reflexivity))).
      seq_inversion. eapply bs_While_True; eassumption.
    + assert (H := IHEXEC _ (ltac:(simpl; reflexivity))).
      apply SmokeTest.seq_assoc in H. seq_inversion. seq_inversion.
      eapply bs_Seq; [eapply bs_While_True; eassumption | assumption].
  - destruct k; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_While_False. assumption.
    + eapply bs_Seq; [apply bs_While_False; assumption | apply IHEXEC; simpl; reflexivity].
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  eapply cps_bs_gen.
  - apply STEP.
  - constructor.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
  eapply cps_bs_gen.
  - apply STEP.
  - constructor.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1.
  - destruct k2; destruct k3; inversion STEP; subst; constructor.
  - destruct k2.
    + apply STEP.
    + apply cps_Seq. apply STEP.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  generalize dependent c3.
  generalize dependent k.
  induction EXEC; intros.
  - (* bs_Skip *)
    assumption.
  - (* bs_Assign *)
    inversion STEP; subst.
    eapply cps_Assign; eassumption.
  - (* bs_Read *)
    inversion STEP; subst.
    apply cps_Read. assumption.
  - (* bs_Write *)
    inversion STEP; subst.
    eapply cps_Write; eassumption.
  - (* bs_Seq *)
    apply cps_Seq.
    apply IHEXEC1.
    apply cps_Skip.
    assert (HK: Kapp k KEmpty = k) by (destruct k; reflexivity).
    apply cps_cont_to_seq.
    rewrite HK.
    apply IHEXEC2.
    assumption.
  - (* bs_If_True *)
    apply cps_If_True.
    + assumption.
    + apply IHEXEC. assumption.
  - (* bs_If_False *)
    apply cps_If_False.
    + assumption.
    + apply IHEXEC. assumption.
  - (* bs_While_True *)
    apply cps_While_True.
    + assumption.
    + apply IHEXEC1.
      apply cps_Skip.
      assert (HK: Kapp k KEmpty = k) by (destruct k; reflexivity).
      apply cps_cont_to_seq.
      rewrite HK.
      apply IHEXEC2.
      assumption.
  - (* bs_While_False *)
    inversion STEP; subst.
    apply cps_While_False; assumption.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont.
  - eassumption.
  - apply cps_Skip.
    apply cps_Empty.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
