Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Import Coq.Program.Equality.
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
  exact H.
Qed.

Definition counter_stmt1 : stmt := (Id 0 ::= Nat 0).
Definition counter_stmt2 : stmt := (Id 0 ::= Nat 1).

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. 
  exists (Id 0 ::= Nat 1), (Id 0 ::= Nat 0). 
  split.
  - unfold eval_equivalent. intros. split; intros.
    + exists [(Id 0, 0%Z)]. dependent destruction H. dependent destruction H. constructor. eauto.
    + exists [(Id 0, 1%Z)]. dependent destruction H. dependent destruction H. constructor. eauto.
  - intro.  
    specialize (H (SeqL Hole (WRITE (Var (Id 0)))) nil (1%Z :: nil)). 
    destruct H. simpl in H, H0.
    assert (G: eval ((Id 0 ::= Nat 1);; WRITE (Var (Id 0))) nil (1%Z :: nil)).
    { exists [(Id 0, 1%Z)]. eapply bs_Seq. econstructor. eauto. econstructor. apply bs_Var. constructor. }
    apply H in G. 
    dependent destruction G. 
    dependent destruction H1. 
    dependent destruction H1_0.
    dependent destruction H1_. 
    dependent destruction VAL0. 
    dependent destruction VAR. 
    inversion VAL. 
    apply H1. reflexivity.
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
    unfold bs_equivalent. intros. split; intros.
    - inversion H. subst. inversion STEP1. subst.
      eapply bs_Seq.
      + exact STEP0.
      + eapply bs_Seq; [exact STEP3 | exact STEP2].
    - inversion H. subst. inversion STEP2. subst.
      eapply bs_Seq.
      + eapply bs_Seq; [exact STEP1 | exact STEP0].
      + exact STEP3.
  Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent. intros. split; intros.
    - inversion H; subst.
      + apply bs_If_True; [assumption | eapply bs_Seq; eassumption].
      + apply bs_If_False; [assumption | apply bs_Skip].
    - inversion H; subst.
      + inversion STEP; subst. eapply bs_While_True; eassumption.
      + inversion STEP; subst. eapply bs_While_False; assumption.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as W.
    remember (st, i, o) as ST.
    induction EXE; try discriminate.
    - (* bs_While_True case *)
      injection HeqW as E1 E2. subst.
      apply IHEXE2; reflexivity.
    - (* bs_While_False case *)
      injection HeqW as E1 E2. subst.
      injection HeqST as E3 E4 E5. subst.
      assumption.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent. intros. split; intros.
    - (* First direction: WHILE (Nat 1) DO SKIP END never terminates *)
      exfalso. 
      remember (WHILE (Nat 1) DO SKIP END) as W.
      induction H; try discriminate.
      + (* bs_While_True case *)
        injection HeqW as E1 E2. subst.
        apply IHbs_int2; reflexivity.
      + (* bs_While_False case *)
        injection HeqW as E1 E2. subst.
        inversion CVAL.
    - (* Second direction: COND (Nat 3) THEN SKIP ELSE SKIP END never terminates *)
      exfalso.
      inversion H; subst; inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent. intros. split; intros.
    - (* Forward direction: s1 -> s2 *)
      remember (WHILE e DO s1 END) as W.
      induction H; try discriminate.
      + (* bs_While_True case *)
        injection HeqW as E1 E2. subst.
        eapply bs_While_True; [eassumption | apply EQ; eassumption | apply IHbs_int2; reflexivity].
      + (* bs_While_False case *)
        injection HeqW as E1 E2. subst.
        eapply bs_While_False; eassumption.
    - (* Backward direction: s2 -> s1 *)
      remember (WHILE e DO s2 END) as W.
      induction H; try discriminate.
      + (* bs_While_True case *)
        injection HeqW as E1 E2. subst.
        eapply bs_While_True; [eassumption | apply EQ; eassumption | apply IHbs_int2; reflexivity].
      + (* bs_While_False case *)
        injection HeqW as E1 E2. subst.
        eapply bs_While_False; eassumption.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro H.
    remember (WHILE (Nat 1) DO s END) as W.
    induction H; try discriminate.
    - injection HeqW as E1 E2. subst.
      apply IHbs_int2; reflexivity.
    - injection HeqW as E1 E2. subst.
      inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof. 
  unfold bs_equivalent. intros. split; intros.
  - inversion H; subst.
    eapply bs_Seq.
    + eassumption.
    + apply EQ; assumption.
  - inversion H; subst.
    eapply bs_Seq.
    + eassumption.
    + apply EQ; assumption.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof. 
  unfold "~~~". intros. split; intros.
  - remember (s1;; s) as S.
    induction H; try discriminate.
    injection HeqS as E1 E2; subst.
    apply bs_Seq with c'. apply EQ. assumption. assumption.
  - remember (s2;; s) as S.
    induction H; try discriminate.
    injection HeqS as E1 E2; subst.
    apply bs_Seq with c'. apply EQ. assumption. assumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. 
  unfold "~~~". intros. split; intros; inversion H; subst.
  - apply bs_If_True. assumption. assumption.
  - apply bs_If_False. assumption. apply EQ. assumption.
  - apply bs_If_True. assumption. assumption.
  - apply bs_If_False. assumption. apply EQ. assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. 
  unfold "~~~". intros. split; intros; inversion H; subst.
  - apply bs_If_True. assumption. apply EQ. assumption.
  - apply bs_If_False. assumption. assumption.
  - apply bs_If_True. assumption. apply EQ. assumption.
  - apply bs_If_False. assumption. assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. 
  unfold "~~~". intros. split; intros.
  - remember (WHILE e DO s1 END) as S.
    induction H; try discriminate.
    + (* bs_While_True case *)
      injection HeqS; intros. subst.
      apply bs_While_True with c'. assumption. apply EQ. assumption.
      apply IHbs_int2. reflexivity.
    + (* bs_While_False case *)
      injection HeqS; intros. subst.
      apply bs_While_False. assumption.
  - remember (WHILE e DO s2 END) as S.
    induction H; try discriminate.
    + (* bs_While_True case *)
      injection HeqS; intros. subst.
      apply bs_While_True with c'. assumption. apply EQ. assumption.
      apply IHbs_int2. reflexivity.
    + (* bs_While_False case *)
      injection HeqS; intros. subst.
      apply bs_While_False. assumption.
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
  generalize dependent c2. induction EXEC1; intros; inversion EXEC2; try reflexivity.
  - f_equal. f_equal. f_equal. apply eval_deterministic with e s; assumption.
  - f_equal. f_equal. f_equal. apply eval_deterministic with e s; assumption.
  - specialize IHEXEC1_1 with c'0. apply IHEXEC1_1 in STEP1. rewrite <- STEP1 in *.
    apply IHEXEC1_2. apply STEP2.
  - apply IHEXEC1. assumption.
  - assert (Z.one = Z.zero). { apply eval_deterministic with e s; assumption. } discriminate.
  - assert (Z.one = Z.zero). { apply eval_deterministic with e s; assumption. } discriminate.
  - apply IHEXEC1. assumption.
  - specialize IHEXEC1_1 with c'0. apply IHEXEC1_1 in STEP. rewrite <- STEP in *.
    apply IHEXEC1_2. apply WSTEP.
  - assert (Z.one = Z.zero). { apply eval_deterministic with e st; assumption. } discriminate.
  - assert (Z.one = Z.zero). { apply eval_deterministic with e st; assumption. } discriminate.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma equiv_update s st1 st2 st1' i i' o o'
      (H1 : equivalent_states st1 st2)
      (H2 : (st1, i, o) == s ==> (st1', i', o'))
  : exists st2', (st2, i, o) == s ==> (st2', i', o') /\ equivalent_states st1' st2'.
Proof.
  dependent induction H2 generalizing st1 st2 st1' i i' o o' H1.
  * (* Case 1 *)
    econstructor.
    split; try eassumption.
    constructor.
  * (* Case 2 *)
    econstructor.
    split.
    - constructor.
      eapply variable_relevance.
      intros.
      apply H1.
      eassumption.
    - split; intro; dependent destruction H; try by constructor.
      all: constructor; try apply H1; assumption.
  * (* Case 3 *)
    econstructor.
    split.
    constructor.
    split; intro; dependent destruction H; try by constructor.
    all: constructor; try apply H1; assumption.
  * (* Case 4 *)
    econstructor.
    split; eauto.
    constructor.
    eapply variable_relevance; eauto.
  * (* Case 5 *)
    destruct c' as ((st'', i''), o'').
    specialize (IHbs_int1 _ _ _ _ _ _ _ H1 JMeq_refl JMeq_refl).
    destruct IHbs_int1 as [st2' [Hstep Hequiv]].
    specialize (IHbs_int2 _ _ _ _ _ _ _ Hequiv JMeq_refl JMeq_refl).
    destruct IHbs_int2 as [st2'' [Hstep2 Hequiv2]].
    econstructor.
    split; eauto.
  * (* Case 6 *)
    specialize (IHbs_int _ _ _ _ _ _ _ H1 JMeq_refl JMeq_refl).
    destruct IHbs_int as [st2' [Hstep Hequiv]].
    econstructor.
    split; eauto.
    apply bs_If_True; eauto.
    eapply variable_relevance; eauto.
  * (* Case 7 *)
    specialize (IHbs_int _ _ _ _ _ _ _ H1 JMeq_refl JMeq_refl).
    destruct IHbs_int as [st2' [Hstep Hequiv]].
    econstructor.
    split; eauto.
    apply bs_If_False; eauto.
    eapply variable_relevance; eauto.
  * (* Case 8 *)
    destruct c' as ((st'', i''), o'').
    specialize (IHbs_int1 _ _ _ _ _ _ _ H1 JMeq_refl JMeq_refl).
    destruct IHbs_int1 as [st2' [Hstep Hequiv]].
    specialize (IHbs_int2 _ _ _ _ _ _ _ Hequiv JMeq_refl JMeq_refl).
    destruct IHbs_int2 as [st2'' [Hstep2 Hequiv2]].
    econstructor.
    split; eauto.
    eapply bs_While_True; eauto.
    eapply variable_relevance; eauto.
  * (* Case 9 *)
    econstructor.
    split; eauto.
    eapply bs_While_False; eauto.
    eapply variable_relevance; eauto.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  specialize (equiv_update _ _ _ _ _ _ _ _ HE1 H).
  intros [st2' [Hstep Hequiv]].
  exists st2'.
  split; exact Hequiv || exact Hstep.
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
    induction EXEC1; intros; inversion EXEC2; subst.
    - reflexivity.
    - assert (z = z0).
      { apply eval_deterministic with e s; assumption. }
      subst. reflexivity.
    - reflexivity.
    - assert (z = z0).
      { apply eval_deterministic with e s; assumption. }
      subst. reflexivity.
    - assert (H_eq: (@None stmt, c') = (@None stmt, c'0)).
      { apply IHEXEC1; assumption. }
      injection H_eq; intros; subst; reflexivity.
    - assert (H_eq: (@None stmt, c') = (Some s1', c'0)).
      { apply IHEXEC1; assumption. }
      discriminate H_eq.
    - assert (H_eq: (Some s1', c') = (@None stmt, c'0)).
      { apply IHEXEC1; assumption. }
      discriminate H_eq.
    - assert (H_eq: (Some s1', c') = (Some s1'0, c'0)).
      { apply IHEXEC1; assumption. }
      injection H_eq; intros; subst; reflexivity.
    - reflexivity.
    - exfalso.
      assert (Z.one = Z.zero).
      { apply eval_deterministic with e s; assumption. }
      discriminate H.
    - exfalso.
      assert (Z.zero = Z.one).
      { apply eval_deterministic with e s; assumption. }
      discriminate H.
    - reflexivity.
    - reflexivity.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''.
    induction STEP1; intros; inversion STEP2; subst;
    match goal with
    | H1: ?c -- ?s --> (@None stmt, ?c1), H2: ?c -- ?s --> (@None stmt, ?c2) |- ?c1 = ?c2 =>
      pose (det := ss_int_step_deterministic s c ((None : option stmt), c1) ((None : option stmt), c2) H1 H2);
      injection det; intros; subst; reflexivity
    | H1: ?c -- ?s --> (@None stmt, ?c1), H2: ?c -- ?s --> (Some ?s', ?c2) |- _ =>
      pose (det := ss_int_step_deterministic s c ((None : option stmt), c1) (Some s', c2) H1 H2);
      discriminate det
    | H1: ?c -- ?s --> (Some ?s', ?c1), H2: ?c -- ?s --> (@None stmt, ?c2) |- _ =>
      pose (det := ss_int_step_deterministic s c (Some s', c1) ((None : option stmt), c2) H1 H2);
      discriminate det
    | H1: ?c -- ?s --> (Some ?s1, ?c1), H2: ?c -- ?s --> (Some ?s2, ?c2) |- _ =>
      pose (det := ss_int_step_deterministic s c (Some s1, c1) (Some s2, c2) H1 H2);
      injection det; intros; subst; apply IHSTEP1; assumption
    end.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    induction s; inversion STEP; subst; constructor; assumption.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    generalize dependent s2.
    generalize dependent c'.
    induction STEP1; intros.
    - apply ss_int_Step with s2 c'.
      + constructor; assumption.
      + assumption.
    - apply ss_int_Step with (s' ;; s2) c'.
      + constructor; assumption.
      + apply IHSTEP1; assumption.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent c''.
    dependent induction s; intros; inversion STEP; subst.
    - eapply bs_Seq.
      + apply ss_bs_base. eassumption.
      + assumption.
    - inversion EXEC; subst. 
      eapply bs_Seq.
      + eapply IHs1; eassumption.
      + assumption.
    - apply bs_If_True; assumption.
    - apply bs_If_False; assumption.
    - inversion EXEC; subst.
      + repeat match goal with
        | H: _ == _ ;; _ ==> _ |- _ => 
          inversion H; clear H; subst;
          try (eapply bs_While_True; eassumption)
        | H: _ == SKIP ==> _ |- _ =>
          inversion H; clear H; subst
        end.
      + repeat match goal with
        | H: _ == SKIP ==> _ |- _ =>
          inversion H; clear H; subst;
          eapply bs_While_False; eassumption
        | H: _ == _ ;; _ ==> _ |- _ => 
          inversion H; clear H; subst
        end.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
  split; intros.
  - induction H; 
    try solve [apply ss_int_Base; constructor; assumption].
    + apply ss_ss_composition with c'; assumption.
    + eapply ss_int_Step.
      * apply ss_If_True. assumption.
      * assumption.
    + eapply ss_int_Step.
      * apply ss_If_False. assumption.
      * assumption.
    + eapply ss_int_Step.
      * constructor. 
      * eapply ss_int_Step.
        -- apply ss_If_True. assumption.
        -- apply ss_ss_composition with c'; assumption.
    + eapply ss_int_Step.
      * constructor.
      * eapply ss_int_Step.
        -- apply ss_If_False. assumption.
        -- apply ss_int_Base. constructor.
        
  - induction H.
    + apply ss_bs_base. assumption.
    + eapply ss_bs_step; eassumption.
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
    induction s; simpl; auto;
    try rewrite Renaming.re_rename_expr; 
    try rewrite Hinv; 
    try rewrite IHs1, IHs2;
    try rewrite IHs;
    auto.
  Qed.
    
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. 
    destruct r. simpl. unfold update. reflexivity. 
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
   Proof. 
    destruct r.
    induction Hbs; simpl.
    - constructor.
    - constructor. apply Renaming.eval_renaming_invariance. assumption.
    - constructor.
    - constructor. apply Renaming.eval_renaming_invariance. assumption.
    - econstructor.
      * apply IHHbs1.
      * apply IHHbs2.
    - eapply bs_If_True.
      * apply Renaming.eval_renaming_invariance. assumption. 
      * apply IHHbs.
    - eapply bs_If_False.
      * apply Renaming.eval_renaming_invariance. assumption. 
      * apply IHHbs.
    - eapply bs_While_True.
      * apply Renaming.eval_renaming_invariance. assumption. 
      * apply IHHbs1.
      * apply IHHbs2.
    - eapply bs_While_False.
      * apply Renaming.eval_renaming_invariance. assumption. 
  Qed.

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r) as [r' Hinv].
    
    assert (Hc: c = rename_conf r' (rename_conf r c)).
    { destruct c as [[st i] o]. simpl.
      rewrite Renaming.re_rename_state; auto. }
      
    assert (Hc': c' = rename_conf r' (rename_conf r c')).
    { destruct c' as [[st' i'] o']. simpl.
      rewrite Renaming.re_rename_state; auto. }
    
    rewrite Hc, Hc'.
    replace s with (rename r' (rename r s)).
    - apply renaming_invariant_bs. assumption.
    - apply re_rename. assumption.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof. 
    split; intros H; destruct H as [x H].
    - exists (Renaming.rename_state r x). 
      apply (renaming_invariant_bs _ _ _ _ H).
    - destruct (Renaming.renaming_inv r) as [r' Hinv].
      exists (Renaming.rename_state r' x).
      replace s with (rename r' (rename r s)).
      * apply (renaming_invariant_bs _ _ _ _ H).
      * apply re_rename. assumption.
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
