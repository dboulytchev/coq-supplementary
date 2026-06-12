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
  unfold contextual_equivalent in H.
  specialize (H Hole).
  simpl in H.
  exact H.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists SKIP, (Id 0 ::= Nat 0).
  split.
  - unfold eval_equivalent, eval.
    intros i o.
    split; intros [st EXEC]; inversion EXEC; subst.
    + exists [(Id 0, 0%Z)]. constructor. constructor.
    + inversion VAL; subst. exists []. constructor.
  - intro CEQ.
    specialize (CEQ (SeqL Hole (WRITE (Var (Id 0))))).
    unfold eval_equivalent, eval in CEQ.
    specialize (CEQ (@nil Z) (0%Z :: nil)).
    destruct CEQ as [_ H].
    assert (EVAL : exists st : state Z,
              ([], [], []) == SKIP;; WRITE (Var (Id 0)) ==> (st, [], 0%Z :: nil)).
    { apply H.
      exists [(Id 0, 0%Z)].
      eapply bs_Seq.
      - apply bs_Assign. constructor.
      - apply bs_Write. constructor. constructor. }
    destruct EVAL as [st EXEC].
    inversion EXEC; subst.
    inversion STEP1; subst.
    inversion STEP2; subst.
    inversion VAL; subst.
    inversion VAR.
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
    split; intro EXEC.
    - inversion EXEC; subst.
      inversion STEP1; subst.
      eapply bs_Seq.
      + exact STEP0.
      + eapply bs_Seq; eauto.
    - inversion EXEC; subst.
      inversion STEP2; subst.
      eapply bs_Seq.
      + eapply bs_Seq; eauto.
      + exact STEP3.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros c c'.
    split; intro EXEC.
    - inversion EXEC; subst.
      + apply bs_If_True; auto.
        eapply bs_Seq; eauto.
      + eapply bs_If_False; eauto.
    - inversion EXEC; subst.
      + inversion STEP; subst.
        eapply bs_While_True; eauto.
      + inversion STEP; subst.
        apply bs_While_False; auto.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (st, i, o) as cf.
    remember (WHILE e DO s END) as w.
    induction EXE; inversion Heqw; subst.
    - eapply IHEXE2; eauto.
    - inversion Heqcf; subst. exact CVAL.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    assert (HLoop : forall c c', ~ c == WHILE (Nat 1) DO SKIP END ==> c').
    { intros c c' EXEC.
      remember (WHILE (Nat 1) DO SKIP END) as w.
      induction EXEC; inversion Heqw; subst.
      - apply IHEXEC2. reflexivity.
      - pose proof (eval_deterministic (Nat 1) st Z.one Z.zero (bs_Nat st 1) CVAL) as HH.
        discriminate HH. }
    split; intro EXEC.
    - exfalso. eapply HLoop; eauto.
    - inversion EXEC; subst; inversion CVAL; lia.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent in *.
    intros c c'.
    split; intro EXEC.
    - remember (WHILE e DO s1 END) as w1.
      revert s2 EQ Heqw1.
      induction EXEC; intros t2 EQ Heqw1; inversion Heqw1; subst.
      + eapply bs_While_True.
        * exact CVAL.
        * match goal with
          | H : _ == s1 ==> _ |- _ == t2 ==> _ => apply EQ; exact H
          end.
        * eapply IHEXEC2; eauto.
      + apply bs_While_False. exact CVAL.
    - remember (WHILE e DO s2 END) as w2.
      revert s1 EQ Heqw2.
      induction EXEC; intros t1 EQ Heqw2; inversion Heqw2; subst.
      + eapply bs_While_True.
        * exact CVAL.
        * match goal with
          | H : _ == s2 ==> _ |- _ == t1 ==> _ => apply EQ; exact H
          end.
        * eapply IHEXEC2; eauto.
      + apply bs_While_False. exact CVAL.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro EXEC.
    remember (WHILE (Nat 1) DO s END) as w.
    induction EXEC; inversion Heqw; subst.
    - apply IHEXEC2. reflexivity.
    - pose proof (eval_deterministic (Nat 1) st Z.one Z.zero (bs_Nat st 1) CVAL) as HH.
      discriminate HH.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro EXEC; inversion EXEC; subst; eapply bs_Seq; eauto; apply EQ; auto.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro EXEC; inversion EXEC; subst; eapply bs_Seq; eauto; apply EQ; auto.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro EXEC; inversion EXEC; subst.
  - eapply bs_If_True; eauto.
  - eapply bs_If_False; eauto. apply EQ; auto.
  - eapply bs_If_True; eauto.
  - eapply bs_If_False; eauto. apply EQ; auto.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro EXEC; inversion EXEC; subst.
  - eapply bs_If_True; eauto. apply EQ; auto.
  - eapply bs_If_False; eauto.
  - eapply bs_If_True; eauto. apply EQ; auto.
  - eapply bs_If_False; eauto.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  apply SmokeTest.while_eq.
  exact EQ.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split.
  - apply eq_congruence_seq_r. exact EQ.
  - split.
    + apply eq_congruence_seq_l. exact EQ.
    + split.
      * apply eq_congruence_cond_else. exact EQ.
      * split.
        -- apply eq_congruence_cond_then. exact EQ.
        -- apply eq_congruence_while. exact EQ.
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
  revert c2 EXEC2.
  induction EXEC1; intros c2 EXEC2; inversion EXEC2; subst; try reflexivity.
  - assert (z = z0) by (eapply eval_deterministic; eauto).
    subst. reflexivity.
  - assert (z = z0) by (eapply eval_deterministic; eauto).
    subst. reflexivity.
  - assert (c'0 = c') by (symmetry; eapply IHEXEC1_1; eauto).
    subst.
    eapply IHEXEC1_2; eauto.
  - eapply IHEXEC1; eauto.
  - eval_zero_not_one.
  - eval_zero_not_one.
  - eapply IHEXEC1; eauto.
  - assert (c'0 = c') by (symmetry; eapply IHEXEC1_1; eauto).
    subst.
    eapply IHEXEC1_2; eauto.
  - eval_zero_not_one.
  - eval_zero_not_one.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma equivalent_states_update (st st' : state Z) x z
      (HE : equivalent_states st st') :
  equivalent_states (st [x <- z]) (st' [x <- z]).
Proof.
  unfold equivalent_states, Expr.equivalent_states.
  intros y n.
  destruct (id_eq_dec x y) as [EQ | NEQ].
  - subst.
    split; intro BIND;
      assert (z = n) by (eapply state_deterministic; [apply update_eq | eauto]);
      subst; apply update_eq.
  - split; intro BIND.
    + apply st_binds_tl; auto.
      destruct (@update_neq Z st x y z n NEQ) as [_ Hstrip].
      destruct (HE y n) as [H _].
      exact (H (Hstrip BIND)).
    + apply st_binds_tl; auto.
      destruct (@update_neq Z st' x y z n NEQ) as [_ Hstrip].
      destruct (HE y n) as [_ H].
      exact (H (Hstrip BIND)).
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')  
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  remember (st1, i, o) as c.
  remember (st2, i', o') as c'.
  revert st1 st1' st2 i o i' o' HE1 Heqc Heqc'.
  induction H; intros stA stA' stB iA oA iB oB HE Heqc Heqc';
    inversion Heqc; inversion Heqc'; subst;
    repeat match goal with
    | H : (_, _, _) = (_, _, _) |- _ => inversion H; clear H; subst
    end.
  - exists stA'. split.
    + exact HE.
    + constructor.
  - assert (VAL' : [| e |] stA' => z).
    { eapply Expr.variable_relevance.
      - intros id _. exact (HE id).
      - exact VAL. }
    exists (stA' [x <- z]).
    split.
    + apply equivalent_states_update. exact HE.
    + apply bs_Assign. exact VAL'.
  - exists (stA' [x <- z]).
    split.
    + apply equivalent_states_update. exact HE.
    + constructor.
  - assert (VAL' : [| e |] stA' => z).
    { eapply Expr.variable_relevance.
      - intros id _. exact (HE id).
      - exact VAL. }
    exists stA'. split.
    + exact HE.
    + apply bs_Write. exact VAL'.
  - destruct c' as [[stm im] om].
    destruct (IHbs_int1 stA stA' stm iA oA im om HE Logic.eq_refl Logic.eq_refl)
      as [stm' [HEm STEPm]].
    destruct (IHbs_int2 stm stm' stB im om iB oB HEm Logic.eq_refl Logic.eq_refl)
      as [stB' [HEB STEPB]].
    exists stB'. split.
    + exact HEB.
    + eapply bs_Seq; eauto.
  - assert (CVAL' : [| e |] stA' => Z.one).
    { eapply Expr.variable_relevance.
      - intros id _. exact (HE id).
      - exact CVAL. }
    destruct (IHbs_int stA stA' stB iA oA iB oB HE Logic.eq_refl Logic.eq_refl)
      as [stB' [HEB STEP']].
    exists stB'. split.
    + exact HEB.
    + eapply bs_If_True; eauto.
  - assert (CVAL' : [| e |] stA' => Z.zero).
    { eapply Expr.variable_relevance.
      - intros id _. exact (HE id).
      - exact CVAL. }
    destruct (IHbs_int stA stA' stB iA oA iB oB HE Logic.eq_refl Logic.eq_refl)
      as [stB' [HEB STEP']].
    exists stB'. split.
    + exact HEB.
    + eapply bs_If_False; eauto.
  - assert (CVAL' : [| e |] stA' => Z.one).
    { eapply Expr.variable_relevance.
      - intros id _. exact (HE id).
      - exact CVAL. }
    destruct c' as [[stm im] om].
    destruct (IHbs_int1 stA stA' stm iA oA im om HE Logic.eq_refl Logic.eq_refl)
      as [stm' [HEm STEP']].
    destruct (IHbs_int2 stm stm' stB im om iB oB HEm Logic.eq_refl Logic.eq_refl)
      as [stB' [HEB WSTEP']].
    exists stB'. split.
    + exact HEB.
    + eapply bs_While_True; eauto.
  - assert (CVAL' : [| e |] stA' => Z.zero).
    { eapply Expr.variable_relevance.
      - intros id _. exact (HE id).
      - exact CVAL. }
    exists stA'. split.
    + exact HE.
    + apply bs_While_False. exact CVAL'.
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
    revert c'' EXEC2.
    induction EXEC1; intros c'' EXEC2; inversion EXEC2; subst; try reflexivity.
    - assert (z = z0) by (eapply eval_deterministic; eauto).
      subst. reflexivity.
    - assert (z = z0) by (eapply eval_deterministic; eauto).
      subst. reflexivity.
    - assert ((None, c') = (None, c'0)) by eauto.
      inversion H. reflexivity.
    - assert ((None, c') = (Some s1', c'0)) by eauto.
      inversion H.
    - assert ((Some s1', c') = (None, c'0)) by eauto.
      inversion H.
    - assert ((Some s1', c') = (Some s1'0, c'0)) by eauto.
      inversion H. reflexivity.
    - eval_zero_not_one.
    - eval_zero_not_one.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    revert c'' STEP2.
    induction STEP1; intros c''0 STEP2; inversion STEP2; subst.
    - pose proof (ss_int_step_deterministic s c (None, c') (None, c''0) H H0) as HH.
      inversion HH. reflexivity.
    - pose proof (ss_int_step_deterministic s c (None, c') (Some s', c'0) H H0) as HH.
      inversion HH.
    - pose proof (ss_int_step_deterministic s c (Some s', c') (None, c''0) H H0) as HH.
      inversion HH.
    - pose proof (ss_int_step_deterministic s c (Some s', c') (Some s'0, c'0) H H0) as HH.
      inversion HH; subst.
      eauto.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP; subst; constructor; auto.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    revert s2 c' STEP2.
    induction STEP1; intros s2 cfin STEP2.
    - eapply ss_int_Step.
      + apply ss_Seq_Compl. exact H.
      + exact STEP2.
    - eapply ss_int_Step.
      + apply ss_Seq_InCompl. exact H.
      + apply IHSTEP1. exact STEP2.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    remember (Some s', c') as r.
    revert s' c' c'' EXEC Heqr.
    induction STEP; intros sx cx cfin EXEC Heqr; inversion Heqr; subst.
    - eapply bs_Seq.
      + eapply ss_bs_base.
        match goal with
        | H : _ -- _ --> (None, _) |- _ => exact H
        end.
      + exact EXEC.
    - inversion EXEC; subst.
      eapply bs_Seq.
      + eapply (IHSTEP s1' cx c'); [exact STEP1 | reflexivity].
      + exact STEP2.
    - eapply bs_If_True; eauto.
    - eapply bs_If_False; eauto.
    - eapply (proj2 (SmokeTest.while_unfolds e s _ cfin)).
      exact EXEC.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split.
    - intro EXEC.
      induction EXEC.
      + apply ss_int_Base. constructor.
      + apply ss_int_Base. constructor. exact VAL.
      + apply ss_int_Base. constructor.
      + apply ss_int_Base. constructor. exact VAL.
      + eapply ss_ss_composition; eauto.
      + eapply ss_int_Step.
        * apply ss_If_True. exact CVAL.
        * exact IHEXEC.
      + eapply ss_int_Step.
        * apply ss_If_False. exact CVAL.
        * exact IHEXEC.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_True. exact CVAL.
          -- eapply ss_ss_composition; eauto.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_False. exact CVAL.
          -- apply ss_int_Base. constructor.
    - intro STEP.
      induction STEP.
      + eapply ss_bs_base; eauto.
      + eapply ss_bs_step; eauto.
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
    induction s; simpl; auto.
    - rewrite Hinv.
      rewrite Expr.Renaming.re_rename_expr with (r := r) (r' := r'); auto.
    - rewrite Hinv. reflexivity.
    - rewrite Expr.Renaming.re_rename_expr with (r := r) (r' := r'); auto.
    - rewrite IHs1, IHs2. reflexivity.
    - rewrite Expr.Renaming.re_rename_expr with (r := r) (r' := r'); auto.
      rewrite IHs1, IHs2. reflexivity.
    - rewrite Expr.Renaming.re_rename_expr with (r := r) (r' := r'); auto.
      rewrite IHs. reflexivity.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    destruct r as [f BF].
    reflexivity.
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r as [f BF].
    induction Hbs; simpl.
    - constructor.
    - apply bs_Assign.
      apply Expr.Renaming.eval_renaming_invariance.
      exact VAL.
    - constructor.
    - apply bs_Write.
      apply Expr.Renaming.eval_renaming_invariance.
      exact VAL.
    - eapply bs_Seq; eauto.
    - eapply bs_If_True; eauto.
      apply Expr.Renaming.eval_renaming_invariance.
      exact CVAL.
    - eapply bs_If_False; eauto.
      apply Expr.Renaming.eval_renaming_invariance.
      exact CVAL.
    - eapply bs_While_True; eauto.
      apply Expr.Renaming.eval_renaming_invariance.
      exact CVAL.
    - apply bs_While_False.
      apply Expr.Renaming.eval_renaming_invariance.
      exact CVAL.
  Qed.

  Lemma re_rename_conf
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (c    : conf) : rename_conf r (rename_conf r' c) = c.
  Proof.
    destruct c as [[st i] o].
    simpl.
    rewrite Expr.Renaming.re_rename_state with (r := r) (r' := r'); auto.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Expr.Renaming.renaming_inv r) as [r' Hinv].
    pose proof (renaming_invariant_bs (rename r s) r' (rename_conf r c) (rename_conf r c') Hbs) as H.
    rewrite re_rename with (r := r') (r' := r) in H; auto.
    rewrite re_rename_conf with (r := r') (r' := r) in H; auto.
    rewrite re_rename_conf with (r := r') (r' := r) in H; auto.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent, eval.
    intros i o.
    split; intros [st EXEC].
    - exists (Expr.Renaming.rename_state r st).
      eapply (renaming_invariant_bs s r) in EXEC.
      exact EXEC.
    - destruct (Expr.Renaming.renaming_inv r) as [r' Hinv].
      exists (Expr.Renaming.rename_state r' st).
      pose proof (renaming_invariant_bs (rename r s) r' ([], i, []) (st, [], o) EXEC) as H.
      simpl in H.
      rewrite re_rename with (r := r') (r' := r) in H; auto.
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
  revert S DEF.
  induction EXEC; intros S DEF; simpl in DEF.
  - inversion DEF.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst.
      constructor.
    + eapply bs_Seq.
      * constructor.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst.
      eapply bs_Assign; eauto.
    + eapply bs_Seq.
      * eapply bs_Assign; eauto.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst.
      constructor.
    + eapply bs_Seq.
      * constructor.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst.
      eapply bs_Write; eauto.
    + eapply bs_Seq.
      * eapply bs_Write; eauto.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + eapply IHEXEC. reflexivity.
    + eapply (proj2 (SmokeTest.seq_assoc s1 s2 _ c c')).
      eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + eapply bs_If_True; eauto.
    + pose proof (IHEXEC _ Logic.eq_refl) as H.
      inversion H; subst.
      eapply bs_Seq.
      * eapply bs_If_True; eauto.
      * exact STEP2.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + eapply bs_If_False; eauto.
    + pose proof (IHEXEC _ Logic.eq_refl) as H.
      inversion H; subst.
      eapply bs_Seq.
      * eapply bs_If_False; eauto.
      * exact STEP2.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + pose proof (IHEXEC (s ;; WHILE e DO s END) Logic.eq_refl) as H.
      inversion H; subst.
      eapply bs_While_True; eauto.
    + pose proof (IHEXEC _ Logic.eq_refl) as H.
      inversion H; subst.
      inversion STEP2; subst.
      eapply bs_Seq.
      * eapply bs_While_True; eauto.
      * exact STEP3.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst.
      apply bs_While_False. exact CVAL.
    + eapply bs_Seq.
      * apply bs_While_False. exact CVAL.
      * eapply IHEXEC. reflexivity.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  eapply cps_bs_gen.
  - exact STEP.
  - reflexivity.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
  eapply cps_bs_gen.
  - exact STEP.
  - reflexivity.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  remember (k2 @ k3) as k.
  revert k2 k3 Heqk.
  induction STEP; intros k2 k3 HK; subst; simpl.
  - destruct k2, k3; simpl in HK; inversion HK; subst; simpl; constructor.
  - destruct k2; simpl.
    + apply cps_Skip. exact STEP.
    + apply cps_Seq. apply cps_Skip. exact STEP.
  - destruct k2; simpl.
    + eapply cps_Assign; eauto.
    + apply cps_Seq. eapply cps_Assign; eauto.
  - destruct k2; simpl.
    + apply cps_Read. exact STEP.
    + apply cps_Seq. apply cps_Read. exact STEP.
  - destruct k2; simpl.
    + eapply cps_Write; eauto.
    + apply cps_Seq. eapply cps_Write; eauto.
  - destruct k2; simpl.
    + apply cps_Seq. exact STEP.
    + apply cps_Seq. apply cps_Seq. exact STEP.
  - destruct k2; simpl.
    + eapply cps_If_True; eauto.
    + apply cps_Seq. eapply cps_If_True; eauto.
  - destruct k2; simpl.
    + eapply cps_If_False; eauto.
    + apply cps_Seq. eapply cps_If_False; eauto.
  - destruct k2; simpl.
    + eapply cps_While_True; eauto.
    + apply cps_Seq. eapply cps_While_True; eauto.
  - destruct k2; simpl.
    + eapply cps_While_False; eauto.
    + apply cps_Seq. eapply cps_While_False; eauto.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  revert c3 k STEP.
  induction EXEC; intros c3 k STEP.
  - exact STEP.
  - inversion STEP; subst.
    eapply cps_Assign; eauto.
  - inversion STEP; subst.
    eapply cps_Read; eauto.
  - inversion STEP; subst.
    eapply cps_Write; eauto.
  - apply cps_Seq.
    assert (H2 : k |- c' -- !s2 --> c3) by (eapply IHEXEC2; exact STEP).
    assert (Hcont : KEmpty |- c' -- !s2 @ k --> c3).
    { destruct k; simpl.
      - apply cps_cont_to_seq with (k2 := KEmpty). exact H2.
      - apply cps_cont_to_seq with (k2 := KStmt s). exact H2. }
    eapply IHEXEC1.
    apply cps_Skip.
    exact Hcont.
  - eapply cps_If_True; eauto.
  - eapply cps_If_False; eauto.
  - eapply cps_While_True; eauto.
    assert (H2 : k |- c' -- !(WHILE e DO s END) --> c3) by (eapply IHEXEC2; exact STEP).
    assert (Hcont : KEmpty |- c' -- !(WHILE e DO s END) @ k --> c3).
    { destruct k; simpl.
      - apply cps_cont_to_seq with (k2 := KEmpty). exact H2.
      - apply cps_cont_to_seq with (k2 := KStmt s0). exact H2. }
    eapply IHEXEC1.
    apply cps_Skip.
    exact Hcont.
  - inversion STEP; subst.
    eapply cps_While_False; eauto.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont.
  - exact EXEC.
  - constructor. constructor.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
