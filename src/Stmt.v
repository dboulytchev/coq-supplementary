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
  unfold contextual_equivalent, eval_equivalent in *.
  intros i o; specialize (H Hole i o); simpl in H; auto.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists ((Id 1) ::= (Nat 2)).
  exists ((Id 1) ::= (Nat 0)).
  split.
  - constructor; intros; inversion H; inversion H0; econstructor; eauto.
  - unfold not. intro. unfold contextual_equivalent in H.
    specialize (H (SeqL Hole (WRITE (Var (Id 1))))).
    simpl in H. unfold eval_equivalent in H.
    specialize (H ([]) ([2%Z])). inversion H. destruct H0.
    + repeat econstructor.
    + inversion H0. subst. inversion STEP1. subst. inversion VAL. subst.
      inversion STEP2. subst. inversion VAL0. subst. inversion VAR. subst.
      inversion H8.
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
      unfold bs_equivalent. intros c c'. split.
      - intros H. inversion H; subst. inversion STEP1; subst.
        apply bs_Seq with c'1. assumption.
        apply bs_Seq with c'0; assumption.
      - intros H. inversion H; subst. inversion STEP2; subst.
        apply bs_Seq with c'1.
        apply bs_Seq with c'0; assumption.
        assumption.
    Qed.

  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent. intros. split. all: intros.
    - inversion H. subst. all: eauto.
    - inversion H. all: subst. all: try inversion STEP. all: eauto.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as prog.
    remember ((st, i, o)) as state.
    induction EXE; inversion Heqprog.
    - subst. apply IHEXE2; reflexivity.
    - inversion Heqstate. subst. assumption.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros. split.
    - intro.
      inversion_clear H. inversion STEP.
      destruct c' eqn:E. destruct p.
      apply (while_false (Nat 1) SKIP s l0 l c'0) in WSTEP.
      inversion WSTEP.
      inversion CVAL.
    - intro.
      inversion_clear H;
      inversion CVAL.
  Qed.
  
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
    Proof.
      split; intros H.
      * remember (WHILE e DO s1 END) as loop1 in H.
        induction H; inversion Heqloop1; subst.
        -- eapply bs_While_True; eauto.
           apply EQ. auto.
        -- apply bs_While_False; auto.
      * remember (WHILE e DO s2 END) as loop2 in H.
        induction H; inversion Heqloop2; subst.
        -- eapply bs_While_True; eauto.
           apply EQ. auto.
        -- apply bs_While_False; auto.
    Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. 
    intros H.
    remember (WHILE Nat 1 DO s END) as loop.
    induction H; try discriminate.
    - inversion Heqloop; subst. 
      apply IHbs_int2; auto.
    - inversion Heqloop; subst.
      inversion CVAL.
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
  unfold bs_equivalent; split; intros H.
  + inversion H; subst.
    apply bs_Seq with (c'0); [ | assumption ].
    destruct (EQ c c'0); auto.
  + inversion H; subst.
    apply bs_Seq with (c'0); [ | assumption ].
    destruct (EQ c c'0); auto.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. 
  split; intros H; inversion H; subst;
    [ apply bs_If_True | apply bs_If_False | apply bs_If_True | apply bs_If_False ];
    auto; apply EQ; auto.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  split; intros H; inversion H; subst;
    try (apply bs_If_True; [ assumption | ]);
    try (apply bs_If_False; [ assumption | ]);
    try (apply EQ; auto); auto.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    apply SmokeTest.while_eq. assumption.
  Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof. 
  split. apply eq_congruence_seq_r. auto.
  split. apply eq_congruence_seq_l. auto.
  split. apply eq_congruence_cond_else. auto.
  split. apply eq_congruence_cond_then. auto.
  apply eq_congruence_while. auto. 
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
    induction EXEC1; intros c2 EXEC2; inversion EXEC2; subst; try reflexivity.
    - by_eval_deterministic.
    - by_eval_deterministic.
    - assert (c' = c'0) by (apply IHEXEC1_1; assumption).
      subst. now apply IHEXEC1_2.
    - now apply IHEXEC1.
    - eval_zero_not_one.
    - eval_zero_not_one.
    - now apply IHEXEC1.
    - assert (c' = c'0) by (apply IHEXEC1_1; assumption).
      subst. now apply IHEXEC1_2.
    - eval_zero_not_one.
    - eval_zero_not_one.
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
Proof. admit. Admitted.
  
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
    induction EXEC1; intros; inversion EXEC2; subst; auto.
    - by_eval_deterministic.
    - by_eval_deterministic.
    - apply IHEXEC1 in SSTEP. inversion SSTEP. auto.
    - apply IHEXEC1 in SSTEP. inversion SSTEP.
    - apply IHEXEC1 in SSTEP. inversion SSTEP.
    - apply IHEXEC1 in SSTEP. inversion SSTEP. auto.
    - eval_zero_not_one.
    - eval_zero_not_one.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
    Proof.
      induction STEP1. 
      - inversion STEP2. 
        + injection (ss_int_step_deterministic s c ((None, c')) ((None, c''))). 
          auto. assumption. assumption.
        + discriminate (ss_int_step_deterministic s c ((None, c')) ((Some s', c'0))).
          assumption. assumption.
      - inversion STEP2.
        + discriminate (ss_int_step_deterministic s c ((None, c'')) ((Some s', c'))).
          assumption. assumption.
        + remember (ss_int_step_deterministic s c ((Some s', c')) ((Some s'0, c'0)) H H0).
          injection e. intros. subst s'0. subst c'0.
          apply IHSTEP1. assumption.
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
    generalize dependent c'. induction STEP1; intros.
    - apply (ss_int_Step _ s2 _ c'). constructor. assumption. assumption.
    - apply (ss_int_Step _ (s' ;; s2) _ c'). constructor. assumption.
      apply IHSTEP1. assumption.
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
      induction s; intros; inversion STEP; intros; subst.
      - apply bs_Seq with (c':=c').
        * apply ss_bs_base. assumption.
        * assumption.
      - inversion EXEC; subst. apply (IHs1 c'0 c' c s1') in SSTEP.
        * apply bs_Seq with (c':=c'0). assumption. assumption.
        * assumption.
      - constructor. assumption. assumption.
      - apply bs_If_False. assumption. assumption.
      - inversion EXEC; subst; destruct c'', p.
        * inversion STEP0; subst. apply (bs_While_True ) with (c':=c').
          assumption. assumption. assumption.
        * inversion STEP0; subst. apply bs_While_False. assumption.
    Qed.
        
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. 
    split.
    - intros. induction  H.
      + apply ss_int_Base. apply ss_Skip.
      + apply ss_int_Base. apply ss_Assign. assumption.
      + apply ss_int_Base. apply ss_Read.
      + apply ss_int_Base. apply ss_Write. assumption.
      + eapply ss_ss_composition. eassumption. assumption.
      + eapply ss_int_Step.
        * apply ss_If_True. assumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_If_False. assumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          ++ apply ss_If_True. assumption.
          ++ inversion H0.
            ** eapply ss_ss_composition. eassumption. assumption.
            ** eapply ss_ss_composition. eassumption. subst c''. assumption.
      + eapply ss_int_Step.
        * eapply ss_While.
        * eapply ss_int_Step.
          ++ apply ss_If_False. assumption.
          ++ apply ss_int_Base. apply ss_Skip.
    - intros. induction H.
      + apply ss_bs_base. assumption.
      + eapply ss_bs_step. eassumption. assumption.
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
    - assert (Renaming.rename_id r (Renaming.rename_id r' i) = i). 
      + apply Hinv.
      + assert (Renaming.rename_expr r (Renaming.rename_expr r' e) = e).
        * apply Renaming.re_rename_expr. trivial.
        * rewrite H. rewrite H0. trivial.
    - assert (Renaming.rename_id r (Renaming.rename_id r' i) = i). 
      + apply Hinv.
      + rewrite -> H. trivial.
    - assert (Renaming.rename_expr r (Renaming.rename_expr r' e) = e). 
      + apply Renaming.re_rename_expr. trivial.
      + rewrite -> H. trivial.
    - rewrite -> IHs1. rewrite -> IHs2. trivial.
    - assert (Renaming.rename_expr r (Renaming.rename_expr r' e) = e).
      + apply Renaming.re_rename_expr. trivial.
      + rewrite H. rewrite IHs1. rewrite IHs2. trivial.
    - assert (Renaming.rename_expr r (Renaming.rename_expr r' e) = e).
      + apply Renaming.re_rename_expr. trivial.
      + rewrite H. rewrite IHs. trivial.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    simpl. unfold Renaming.rename_id. destruct r. reflexivity.
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    induction Hbs; simpl; destruct r eqn:Hr.
    - constructor.
    - constructor. apply Renaming.eval_renaming_invariance. auto.
    - constructor.
    - constructor. apply Renaming.eval_renaming_invariance. auto.
    - econstructor.
      * apply IHHbs1.
      * apply IHHbs2.
    - constructor. apply Renaming.eval_renaming_invariance.
      * auto.
      * apply IHHbs.
    - apply bs_If_False. apply Renaming.eval_renaming_invariance.
      * auto.
      * apply IHHbs.
    - eapply bs_While_True. apply Renaming.eval_renaming_invariance.
      * auto.
      * apply IHHbs1.
      * apply IHHbs2.
    - eapply bs_While_False. apply Renaming.eval_renaming_invariance. auto.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    remember (Renaming.renaming_inv r) as inv_r eqn:Heq.
    destruct inv_r as [x Hinv].
    apply (renaming_invariant_bs _ x) in Hbs.
    rewrite (re_rename x r Hinv) in Hbs.
    destruct c as [[s1 i1] o1], c' as [[s2 i2] o2].
    simpl in Hbs.
    rewrite !Renaming.re_rename_state in Hbs; auto.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent. unfold eval. split; intros.
    - destruct H. apply (renaming_invariant_bs _ r) in H.
      simpl in H. exists (Renaming.rename_state r x). auto.
    - destruct H.
      remember (Renaming.renaming_inv2 r). destruct e.
      rewrite <- (Renaming.re_rename_state r x0 r0 ([])) in H.
      rewrite <- (Renaming.re_rename_state r x0 r0 x) in H.
      apply (renaming_invariant_bs_inv s r ((Renaming.rename_state x0 ([])), i, []) ((Renaming.rename_state x0 x), [], o)) in H.
      simpl in H.
      exists (Renaming.rename_state x0 x). auto.
  Qed.
  
End Renaming.
