Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

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
  remember (Id 0 ::= Nat Z.zero). remember (Id 0 ::= Nat Z.one).
  exists s, s0. split.
    - intro. intro. split; intro.
      + inversion H. subst. inversion H0. exists [(Id 0, Z.one)]. apply bs_Assign. apply bs_Nat.
      + inversion H. subst. inversion H0. exists [(Id 0, Z.zero)]. apply bs_Assign. apply bs_Nat.
    - intro. remember (SeqL Hole (COND Var (Id 0) THEN WRITE (Nat Z.one) ELSE WRITE (Nat Z.zero) END)). specialize (H c ([]) ([Z.one])). destruct H. clear H.
      assert (<| c <~ s0 |> [] => [Z.one]). subst. simpl. exists [(Id 0, Z.one)]. 
      apply bs_Seq with ([(Id 0, Z.one)], [], []). apply bs_Assign. apply bs_Nat. apply bs_If_True. apply bs_Var. apply st_binds_hd. apply bs_Write. apply bs_Nat.
      specialize (H0 H). subst. clear H.
        inversion_clear H0. inversion_clear H. inversion STEP1. inversion VAL. subst. clear VAL STEP1.
        inversion_clear STEP2.
          + inversion CVAL. inversion VAR. contradiction.
          + inversion STEP. inversion VAL.
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
    split; intros; seq_inversion; seq_inversion; seq_apply.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. 
    unfold bs_equivalent.
    intros.
    split.
    - intro.
      inversion_clear H.
      + apply bs_If_True. auto. econstructor. eauto. auto. 
      + apply bs_If_False. auto. constructor.
    - intro.
      inversion_clear H.
      inversion_clear STEP.
      econstructor.
      eauto. eauto. eauto.
      destruct c'. destruct p.
      inversion STEP.
      apply bs_While_False.
      clear - H CVAL.
      subst. exact CVAL.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof. 
    remember (WHILE e DO s END).
    remember (st, i, o).
    induction EXE; inversion Heqs0.
    - apply IHEXE2. auto. auto. 
    - inversion Heqp. subst. auto. 
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
     inversion WSTEP. inversion CVAL.
    - intro.
      inversion_clear H.
      all: (inversion_clear STEP; destruct c' eqn:E; destruct p; apply bs_While_False; inversion CVAL).
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof. 
    unfold bs_equivalent.
    split; intros;
    [ remember (WHILE e DO s1 END) | remember (WHILE e DO s2 END) ];
    induction H; inversion Heqs;
    econstructor; subst; eauto; subst;
    unfold bs_equivalent in EQ;
    apply EQ in H; eauto.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. 
    unfold not. intro. 
    remember (WHILE Nat 1 DO s END). 
    induction H; inversion Heqs0; subst.
    - eapply IHbs_int2. eauto. 
    - inversion CVAL. 
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof. 
  unfold bs_equivalent. unfold bs_equivalent in EQ.
  intros c c'. split.
  all: (intro H; seq_inversion; specialize (EQ c'0 c'); apply EQ in STEP2; seq_apply).
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof. 
  unfold bs_equivalent. unfold bs_equivalent in EQ.
  intros. split.
  all: (intro; seq_inversion; specialize (EQ c c'0); apply EQ in STEP1; seq_apply).
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent. intros c c'.
  split; intros H; inversion H; subst.
  - apply bs_If_True; try assumption.
  - apply bs_If_False; try assumption; apply EQ; assumption.
  - apply bs_If_True; try assumption.
  - apply bs_If_False; try assumption; apply EQ; assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. 
  unfold bs_equivalent. intros c c'.
  split; intros H; inversion H; subst.
  - apply bs_If_True; try assumption; apply EQ; assumption.
  - apply bs_If_False; try assumption.
  - apply bs_If_True; try assumption; apply EQ; assumption.
  - apply bs_If_False; try assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. 
  apply SmokeTest.while_eq. auto.
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
  induction EXEC1; intros; inversion EXEC2; auto.
  - apply (eval_deterministic e s z z0) in VAL. subst z. auto. auto. 
  - apply (eval_deterministic e s z z0) in VAL. subst z. auto. auto. 
  - apply IHEXEC1_1 in STEP1. subst c'0. apply IHEXEC1_2 in STEP2. auto. 
  - eval_zero_not_one.
  - eval_zero_not_one. 
  - apply IHEXEC1_1 in STEP. subst c'0. apply IHEXEC1_2 in WSTEP. auto. 
  - eval_zero_not_one. 
  - eval_zero_not_one. 
Qed.
  
(* Contextual equivalence is equivalent to the semantic one *)
(* TODO: no longer needed *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); assumption.

Lemma eq_eq_ceq s1 s2: s1 ~~~ s2 <-> s1 ~c~ s2.
Proof. admit. Admitted.

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
    induction EXEC2; intros.
    - inversion EXEC1. auto. 
    - inversion EXEC1.
      subst. apply (eval_deterministic e s z z0) in SVAL. subst z.
      auto. auto.
    - inversion EXEC1. auto.
    - inversion EXEC1.
      auto.
      apply (eval_deterministic e s z z0) in SVAL.
      subst z. auto. auto.
    - inversion EXEC1. inversion EXEC2;
      specialize (IHEXEC2 (None, c'1));
      apply IHEXEC2 in SSTEP; inversion SSTEP; auto; subst c'; auto.
      specialize (IHEXEC2 (Some s1', c'1)).
      apply IHEXEC2 in SSTEP. inversion SSTEP.
    - inversion EXEC1. inversion EXEC2;
      specialize (IHEXEC2 (None, c'1));
      apply IHEXEC2 in SSTEP; inversion SSTEP; auto; subst c'; auto.
      specialize (IHEXEC2 (Some s1'0, c'1)).
      apply IHEXEC2 in SSTEP. inversion SSTEP. auto.
    - inversion EXEC1. auto. eval_zero_not_one. 
    - inversion EXEC1. eval_zero_not_one. auto. 
    - inversion EXEC1. auto.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof. 
    generalize dependent c''.
    induction STEP1. 
    - intros c'' STEP2. inversion STEP2.
      + apply ss_int_step_deterministic with (c':=(None, c'')) in H.
        inversion H. reflexivity. auto.
      + apply ss_int_step_deterministic with (c':=(Some s', c'0)) in H.
        inversion H. auto.
    - intros c''0 STEP2. inversion STEP2.
      + apply ss_int_step_deterministic with (c':=(None, c''0)) in H.
        inversion H. auto.
      + apply ss_int_step_deterministic with (c':=(Some s'0, c'0)) in H.
        inversion H. subst. apply IHSTEP1 in H1. auto. auto.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. 
    remember (None, c') as c'' eqn:Heq.
    induction STEP; inversion Heq.
    - apply bs_Skip. 
    - apply bs_Assign. auto. 
    - apply bs_Read. 
    - apply bs_Write. auto. 
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof. 
    generalize dependent c'.
    induction STEP1; intros c'0 Hst.
    - apply ss_int_Step with (s2) (c').
      apply ss_Seq_Compl. auto. auto.
    - apply ss_int_Step with (s' ;; s2) (c').
      apply ss_Seq_InCompl. auto.
      apply IHSTEP1 in Hst. auto.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof. 
    generalize dependent EXEC.
    generalize dependent STEP.
    generalize dependent c''.
    generalize dependent c'.
    generalize dependent c.
    generalize dependent s'.
    induction s; intros s' c c' c'' STEP EXEC.
    1-4 : inversion STEP.
    - inversion STEP.
        + apply ss_bs_base in SSTEP. seq_apply.
        + subst s'. inversion EXEC. subst.
          apply IHs1 with (c'':=c'1) in SSTEP. seq_apply. auto.
    - inversion STEP.
      + apply bs_If_True. auto. subst. auto. 
      + apply bs_If_False. auto. subst. auto. 
    - inversion STEP.
      subst s'. inversion EXEC; subst.
      + inversion STEP0. subst.
        apply bs_While_True with (c').
        auto. auto. auto.
      + inversion STEP0.
        apply bs_While_False.
        auto.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. 
    split; intro.
    - induction H.
      + apply ss_int_Base. apply ss_Skip.
      + apply ss_int_Base. apply ss_Assign. exact VAL.
      + apply ss_int_Base. apply ss_Read.
      + apply ss_int_Base. apply ss_Write. exact VAL.
      + apply ss_ss_composition with c'. exact IHbs_int1. exact IHbs_int2.
      + apply ss_int_Step with s1 (s, i, o). apply ss_If_True.  exact CVAL. exact IHbs_int.
      + apply ss_int_Step with s2 (s, i, o). apply ss_If_False. exact CVAL. exact IHbs_int.
      + apply ss_int_Step with (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (st, i, o). apply ss_While.
        apply ss_int_Step with (s ;; WHILE e DO s END) (st, i, o). 
        apply ss_If_True. exact CVAL. apply ss_ss_composition with c'. 
        exact IHbs_int1. exact IHbs_int2.
      + apply ss_int_Step with (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (st, i, o). apply ss_While.
        apply ss_int_Step with SKIP (st, i, o). 
        apply ss_If_False. exact CVAL. apply ss_int_Base. apply ss_Skip.
    - induction H.
      + apply ss_bs_base. exact H.
      + apply ss_bs_step with c' s'. exact H. exact IHss_int.
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
    reflexivity.
      assert (Renaming.rename_id r (Renaming.rename_id r' i) = i). apply Hinv.
      assert (Renaming.rename_expr r (Renaming.rename_expr r' e) = e). apply Renaming.re_rename_expr. exact Hinv.
    rewrite -> H. rewrite -> H0. reflexivity.
      assert (Renaming.rename_id r (Renaming.rename_id r' i) = i). apply Hinv.
    rewrite -> H. reflexivity.
      assert (Renaming.rename_expr r (Renaming.rename_expr r' e) = e). apply Renaming.re_rename_expr. exact Hinv.
    rewrite -> H. reflexivity.
    rewrite -> IHs1. rewrite -> IHs2. reflexivity.
      assert (Renaming.rename_expr r (Renaming.rename_expr r' e) = e). apply Renaming.re_rename_expr. exact Hinv.
    rewrite -> H. rewrite -> IHs1. rewrite -> IHs2. reflexivity.
      assert (Renaming.rename_expr r (Renaming.rename_expr r' e) = e). apply Renaming.re_rename_expr. exact Hinv.
    rewrite -> H. rewrite -> IHs. reflexivity.
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
    destruct r. induction Hbs.
    - apply bs_Skip.
    - apply bs_Assign. apply Renaming.eval_renaming_invariance. exact VAL.
    - apply bs_Read.
    - apply bs_Write. apply Renaming.eval_renaming_invariance. exact VAL.
    - apply bs_Seq with (rename_conf (exist _ x b) c'). exact IHHbs1. exact IHHbs2.
    - apply bs_If_True. apply Renaming.eval_renaming_invariance. exact CVAL. exact IHHbs.
    - apply bs_If_False. apply Renaming.eval_renaming_invariance. exact CVAL. exact IHHbs.
    - apply bs_While_True with (rename_conf (exist _ x b) c'). apply Renaming.eval_renaming_invariance. exact CVAL. exact IHHbs1. exact IHHbs2.
    - apply bs_While_False. apply Renaming.eval_renaming_invariance. exact CVAL.
  Qed.
  
  Lemma re_rename_conf (r r' : renaming) (Hinv : Renaming.renamings_inv r r') (c : conf) : rename_conf r (rename_conf r' c) = c.
  Proof. 
    destruct c, p. simpl. 
    assert (Renaming.rename_state r (Renaming.rename_state r' s) = s). 
    apply Renaming.re_rename_state. 
    - exact Hinv. 
    - rewrite -> H. reflexivity. 
  Qed.

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof. 
    destruct (Renaming.renaming_inv r) as [r' Hinv].
    rewrite <- (re_rename r' r Hinv s). rewrite <- (re_rename_conf r' r Hinv c). rewrite <- (re_rename_conf r' r Hinv c').
    apply renaming_invariant_bs. apply Hbs.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof. 
    intro. intro. split; intro.
    inversion H. exists (Renaming.rename_state r x).
    assert (rename_conf r ([], i, []) = ([], i, [])).
    - reflexivity.
    - assert (rename_conf r (x, [], o) = (Renaming.rename_state r x, [], o)).
      + reflexivity.
      + rewrite <- H1. rewrite <- H2. apply renaming_invariant_bs. exact H0.
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
    
Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof. 
  generalize dependent S.
  induction EXEC; intros.
  - inversion DEF. 
  - cps_bs_gen_helper k DEF bs_Skip. 
  - cps_bs_gen_helper k DEF bs_Assign. 
  - cps_bs_gen_helper k DEF bs_Read. 
  - cps_bs_gen_helper k DEF bs_Write. 
  - destruct k.
    + apply (IHEXEC S). apply DEF. 
    + inversion DEF.
      apply SmokeTest.seq_assoc.
      apply IHEXEC. auto. 
  - destruct k; inversion DEF.
    + subst. apply bs_If_True.
      auto. auto.
    + assert ((s, i, o) == s1 ;; s0 ==> (c')).
      * apply IHEXEC. auto. 
      * inversion H. subst.
        apply bs_Seq with (c'0). apply bs_If_True.
        auto. auto. auto.
  - destruct k; inversion DEF.
    + subst. apply bs_If_False. auto. auto. 
    + assert ((s, i, o) == s2 ;; s0 ==> (c')).
      * apply IHEXEC. auto. 
      * inversion H. subst.
        apply bs_Seq with (c'0). apply bs_If_False.
        auto. auto. auto.
  - destruct k; inversion DEF.
    + subst.
      assert ((st, i, o) == s ;; (WHILE e DO s END) ==> c').
      * auto. 
      * inversion H. subst.
        apply bs_While_True with (c'0).
        auto. auto. auto.
    + subst.
      assert ((st, i, o) == s ;; (WHILE e DO s END) ;; s0 ==> c').
      * auto. 
      * inversion H. subst.
        inversion_clear STEP2. apply bs_Seq with (c'1).
        apply bs_While_True with (c'0).
        auto. auto. auto. auto.
  - cps_bs_gen_helper k DEF bs_While_False. 
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. 
  remember !(s1 ;; s2).
  eapply cps_bs_gen. eauto.
  unfold Kapp.
  reflexivity.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. 
  remember !(s) @ KEmpty.
  eapply cps_bs_gen.
  eauto.
  unfold Kapp.
  reflexivity.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. 
  destruct k1; destruct k2; unfold Kapp.
  - auto.
  - destruct k3; unfold Kapp in STEP; inversion STEP. 
  - unfold Kapp in STEP. auto. 
  - apply cps_Seq. auto. 
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. 
  inversion_clear STEP. subst. 
  generalize dependent k. generalize c3. 
  induction EXEC; intros.
  - apply cps_Skip. exact CSTEP.
  - apply cps_Assign with z. exact VAL. exact CSTEP.
  - apply cps_Read. exact CSTEP.
  - apply cps_Write with z. exact VAL. exact CSTEP.
  - apply cps_Seq. apply IHEXEC1. destruct k. apply IHEXEC2. exact CSTEP. apply cps_Seq. apply IHEXEC2. exact CSTEP.
  - apply cps_If_True. exact CVAL. apply IHEXEC. exact CSTEP.
  - apply cps_If_False. exact CVAL. apply IHEXEC. exact CSTEP.
  - apply cps_While_True. exact CVAL. apply IHEXEC1. destruct k. apply IHEXEC2. exact CSTEP. apply cps_Seq. apply IHEXEC2. exact CSTEP.
  - apply cps_While_False. exact CVAL. exact CSTEP.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. 
  apply bs_int_to_cps_int_cont with c'. 
  - exact EXEC. 
  - apply cps_Skip. apply cps_Empty. 
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
