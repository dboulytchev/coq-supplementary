Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

From hahn Require Import HahnBase.
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
  unfold contextual_equivalent in H.
  apply (H Hole).
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. 
  exists (Assn (Id 0) (Nat 1)), (Assn (Id 0) (Nat 2)).
  split.
  - unfold eval_equivalent; intros.
    split; intros; unfold eval in *.
    + exists [(Id 0, 2%Z)].
      destruct H as [st H].
      inversion H; subst.
      constructor. auto.
    + exists [(Id 0, 1%Z)].
      destruct H as [st H].
      inversion H; subst.
      constructor. auto.
  - intros H.
    unfold contextual_equivalent, eval_equivalent in H.
    specialize (H (SeqL Hole (WRITE (Var (Id 0))))).
    specialize (H ([]) ([1%Z])).
    unfold plug in H.
    inversion H; subst.
    destruct H0.
    + repeat econstructor.
    + inversion H0; subst.
      inversion STEP1; subst. 
      inversion STEP2; subst.
      inversion VAL; subst.
      inversion VAL0; subst.
      inversion VAR; subst.
      destruct H7.
      reflexivity.
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
    unfold bs_equivalent; intros.
    split; intros.
    - repeat seq_inversion. repeat econstructor; eauto.
    - repeat seq_inversion. repeat econstructor; eauto.
  Qed.
  
  (* One-step unfolding *) 
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent; intros.
    split; intros.
    - inversion H; subst.
      + econstructor. eauto. econstructor. eauto. assumption.
      + eauto.
    - dependent destruction H.
      + dependent destruction H. econstructor. 
        assumption. exact H. assumption.
      + dependent destruction H.
        apply bs_While_False. assumption.
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    dependent induction EXE.
    - eauto.
    - assumption. 
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent; intros.
    split; intros.
    - dependent induction H.
      + assert (WHILE Nat 1 DO SKIP END = WHILE Nat 1 DO SKIP END) by reflexivity.
        specialize (IHbs_int2 H1).
        inversion H. subst. assumption.
      + inversion CVAL.
    - dependent destruction H; inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent; intros.
    split; intros.
    - dependent induction H.
      + eapply bs_While_True.
        * assumption.
        * apply EQ; exact H.
        * eapply IHbs_int2.
          -- exact EQ.
          -- reflexivity.
      + eapply bs_While_False. assumption.
    - dependent induction H.
      + eapply bs_While_True.
        * assumption.
        * apply EQ; exact H.
        * eapply IHbs_int2.
          -- exact EQ.
          -- reflexivity.
      + eapply bs_While_False. assumption.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intros H.
    dependent induction H.
    - assert (WHILE Nat 1 DO s END = WHILE Nat 1 DO s END) by reflexivity.
      specialize (IHbs_int2 s H1).
      assumption.
    - inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent in *.
  split; intros H;
    dependent destruction H;
    specialize (EQ c' c'');
    apply EQ in H0;
    eauto.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent in *.
  split; intros H;
    dependent destruction H;
    specialize (EQ c c');
    apply EQ in H;
    eauto.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent in *.
  split; intros H.
  - dependent destruction H.
    + apply bs_If_True; auto.
    + apply bs_If_False; auto.
      apply (EQ (s0, i, o) c') in H.
      assumption.
  - dependent destruction H.
    + apply bs_If_True; auto.
    + apply bs_If_False; auto.
      apply (EQ (s0, i, o) c') in H.
      assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent in *.
  split; intros H.
  - dependent destruction H.
    + apply bs_If_True; auto.
      apply (EQ (s0, i, o) c') in H.
      assumption.
    + apply bs_If_False; auto.
  - dependent destruction H.
    + apply bs_If_True; auto.
      apply (EQ (s0, i, o) c') in H.
      assumption.
    + apply bs_If_False; auto.  
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  unfold bs_equivalent in *.
  split; intros H.
  - dependent induction H.
    + eapply bs_While_True; auto.
      * apply (EQ (st, i, o) c') in H. exact H.
      * assert (WHILE e DO s1 END = WHILE e DO s1 END) by reflexivity.
        specialize (IHbs_int2 e s1 EQ H1).
        assumption.
    + apply bs_While_False; auto.
  - dependent induction H.
    + eapply bs_While_True; auto.
      * apply (EQ (st, i, o) c') in H. exact H.
      * assert (WHILE e DO s2 END = WHILE e DO s2 END) by reflexivity.
        specialize (IHbs_int2 e s2 EQ H1).
        assumption.
    + apply bs_While_False; auto.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. apply eq_congruence_seq_r. exact EQ.
  split. apply eq_congruence_seq_l. exact EQ.
  split. apply eq_congruence_cond_else. exact EQ.
  split. apply eq_congruence_cond_then. exact EQ.
  apply eq_congruence_while. exact EQ.
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
  dependent induction EXEC2; intros.
  all: inversion EXEC1; subst; auto.
  all: try by_eval_deterministic.
  all: try eval_zero_not_one.
  - specialize (IHEXEC2_1 c'0 STEP1); rewrite IHEXEC2_1 in *.
    specialize (IHEXEC2_2 c1 STEP2); assumption.
  - specialize (IHEXEC2_1 c'0 STEP); rewrite IHEXEC2_1 in *.
    specialize (IHEXEC2_2 c1 WSTEP); assumption.
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
  - eauto.
  - exists (st1' [x <- z]); split; intros.
    + split; intros.
      * inversion H; subst.
        -- constructor.
        -- apply st_binds_tl. assumption.
           specialize (HE1 id z0).
           destruct HE1.
           specialize (H0 H6).
           assumption.
      * dependent destruction H.
        -- constructor.
        -- apply st_binds_tl. assumption.
           specialize (HE1 id x0).
           destruct HE1.
           specialize (H2 H0).
           assumption.
    + constructor. eapply variable_relevance; auto.
  - exists (st1' [x <- z]); split; intros.
    + split; intros.
      * inversion H; subst.
        -- constructor.
        -- apply st_binds_tl. assumption.
           specialize (HE1 id z0).
           destruct HE1.
           specialize (H0 H6).
           assumption.
      * dependent destruction H.
        -- constructor.
        -- apply st_binds_tl. assumption.
           specialize (HE1 id x0).
           destruct HE1.
           specialize (H2 H0).
           assumption.
    + constructor.
  - exists st1'.
    split; auto.
    constructor. 
    eapply variable_relevance; auto.
  - destruct c' as [[st'' i''] o''].
    assert ((st1, i, o) ~= (st1, i, o)) by reflexivity.
    assert ((st'', i'', o'') ~= (st'', i'', o'')) by reflexivity.
    assert ((st2, i', o') ~= (st2, i', o')) by reflexivity.
    specialize (IHbs_int1 i o i'' o'' st1 st'' H1 H2 st1' HE1).
    destruct IHbs_int1 as [st2' [HE2 HE3]].
    assert (equivalent_states st'' st2').
    { admit. }
    specialize (IHbs_int2 i'' o'' i' o' st'' st2 H2 H3 st2' H4).
    destruct IHbs_int2 as [st2'' [HE4 HE5]].
    exists st2''.
    split; auto.
    econstructor.
    exact HE3.
    exact HE5.
  - assert ((st1, i, o) ~= (st1, i, o)) by reflexivity.
    assert ((st2, i', o') ~= (st2, i', o')) by reflexivity.
    specialize (IHbs_int i o i' o' st1 st2 H0 H1 st1' HE1).
    destruct IHbs_int as [st2' [HE2 HE3]].
    exists st2'.
    split; auto.
    constructor; auto.
    eapply variable_relevance; auto.
  - assert ((st1, i, o) ~= (st1, i, o)) by reflexivity.
    assert ((st2, i', o') ~= (st2, i', o')) by reflexivity.
    specialize (IHbs_int i o i' o' st1 st2 H0 H1 st1' HE1).
    destruct IHbs_int as [st2' [HE2 HE3]].
    exists st2'.
    split; auto.
    apply bs_If_False; auto.
    eapply variable_relevance; auto.
Abort.
  
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
    dependent induction s; intros.
    all: inversion EXEC1; subst; inversion EXEC2; subst; eauto.
    all: try (by_eval_deterministic; eauto).
    all: try (eval_zero_not_one; eauto).
    all: try (specialize (IHs1 c _ _ SSTEP SSTEP0); inversion IHs1; subst; eauto).
  Qed.
    
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    dependent induction STEP1; dependent destruction STEP2; eauto.
    all: try (remember (ss_int_step_deterministic _ _ _ _ H H0) as EQ; inversion EQ; subst; eauto).
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP; subst; eauto.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    dependent induction STEP1; eauto.
    - apply ss_int_Step with (s' := s2) (c' := c'0).
      + apply ss_Seq_Compl. assumption.
      + assumption.
    - apply ss_Seq_InCompl with (s2 := s2) in H.
      apply IHSTEP1 in STEP2.
      eapply ss_int_Step.
      + exact H.
      + assumption.
  Qed. 
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent c''.
    generalize dependent c'.
    generalize dependent c.
    dependent induction s; intros.
    all: try (inversion STEP; subst; eauto). 
    - apply bs_Seq with (c' := c').
      + inversion s1; subst; inversion SSTEP; subst; eauto.
      + assumption.
    - inversion EXEC; subst.
      specialize (IHs1 s1' c c' SSTEP c'0 STEP1).
      apply bs_Seq with (c' := c'0).
      + assumption.
      + assumption.
    - inversion EXEC; subst.
      + inversion STEP0; subst.
        apply bs_While_True with (c' := c'); assumption.
      + inversion STEP0; subst.
        apply bs_While_False; assumption.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intros.
    - dependent induction H; intros.
      + apply ss_int_Base; constructor.
      + apply ss_int_Base; constructor; eauto.
      + apply ss_int_Base; constructor; eauto.
      + apply ss_int_Base; constructor; eauto.
      + apply ss_ss_composition with (c'' := c'); assumption.
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
          -- apply ss_ss_composition with (c'' := c'); assumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_False. assumption.
          -- constructor. constructor.
    - dependent induction H; intros.
      + inversion H; subst; constructor; assumption.
      + apply ss_bs_step with (c' := c') (s' := s'); assumption.  
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
    unfold Renaming.renamings_inv in Hinv.
    induction s; simpl; auto.
    all: try (rewrite Hinv; auto).
    all: try (rewrite Renaming.re_rename_expr; auto).
    all: try (rewrite IHs1; rewrite IHs2; auto).
    - rewrite IHs; auto.
  Qed.

  Lemma re_rename_conf 
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (c    : conf) : rename_conf r (rename_conf r' c) = c.
  Proof.
    unfold rename_conf.
    unfold rename.
    destruct c as [[st i] o].
    simpl.
    rewrite Renaming.re_rename_state; auto.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    unfold update.
    rewrite Renaming.rename_simpl.
    reflexivity.
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    dependent induction Hbs; intros.
    - simpl; auto.
    - unfold rename_conf.
      unfold rename.
      rewrite rename_state_update_permute.
      constructor.
      rewrite <- Renaming.eval_renaming_invariance.
      assumption.
    - unfold rename_conf.
      unfold rename.
      rewrite rename_state_update_permute.
      constructor.
    - unfold rename_conf.
      unfold rename.
      constructor. 
      rewrite <- Renaming.eval_renaming_invariance.
      assumption.
    - apply bs_Seq with (c' := (rename_conf r c')); assumption.
    - apply bs_If_True.
      + rewrite <- Renaming.eval_renaming_invariance.
        assumption.
      + assumption.
    - apply bs_If_False.
      + rewrite <- Renaming.eval_renaming_invariance.
        assumption.
      + assumption.
    - apply bs_While_True with (c' := (rename_conf r c')).
      + rewrite <- Renaming.eval_renaming_invariance.
        assumption.
      + assumption.
      + assumption.
    - apply bs_While_False.
      + rewrite <- Renaming.eval_renaming_invariance.
        assumption.
  Qed.
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    pose proof (Renaming.renaming_inv3 r) as [r' [Hinv Hinv']].
    pose proof (re_rename_conf r' r Hinv) as Hc.
    pose proof (re_rename_conf r r' Hinv') as Hc'.
    rewrite <- (Hc c) in *.
    rewrite <- (Hc c') in *.
    rewrite (Hc' (rename_conf r c)) in Hbs.
    rewrite (Hc' (rename_conf r c')) in Hbs.
    pose proof (re_rename r' r Hinv) as Hs.
    pose proof (re_rename r r' Hinv') as Hs'.
    rewrite <- (Hs s) in *.
    rewrite (Hs' (rename r s)) in Hbs.
    apply renaming_invariant_bs.
    assumption.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent, contextual_equivalent.
    intros.
    split; intros H.
    - destruct H.
      exists (Renaming.rename_state r x).
      apply (renaming_invariant_bs s r ([], i, []) (x, [], o)); auto.
    - destruct H.
      pose proof (Renaming.renaming_inv3 r) as [r' [Hinv Hinv']].
      rewrite <- (Renaming.re_rename_state r r' Hinv' x) in H.
      exists (Renaming.rename_state r' x).
      apply (renaming_invariant_bs_inv s r ([], i, []) ((Renaming.rename_state r' x), [], o)); auto.
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
Proof. admit. Admitted.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. admit. Admitted.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. admit. Admitted.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. admit. Admitted.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. admit. Admitted.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. admit. Admitted.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
