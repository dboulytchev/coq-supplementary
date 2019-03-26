Require Import List.
Import ListNotations.
Require Import Omega.

From Bignums Require Export BigZ.
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
Definition conf :=  (state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "c1 '==' s '==>' c2" (at level 0).

Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
| bs_Skip        : forall (c : conf),
    c == SKIP ==> c 
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

(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf),
    c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Definition bs_implies (s1 s2 : stmt) :=
  forall (c c' : conf),
    c == s1 ==> c' -> c == s2 ==> c'.

Notation "s1 '~~>' s2" := (bs_implies s1 s2) (at level 0).

Lemma bs_2impl_eq (s1 s2 : stmt) :
  (s1 ~~> s2) -> (s2 ~~> s1) -> (s1 ~~~ s2).
Proof.
  unfold bs_implies.
  unfold bs_equivalent.
  intros H1 H2.
  intros c c'.
  split.
  - apply H1.
  - apply H2.
Qed.

Lemma bs_eq_symm (s1 s2 : stmt) :
  (s1 ~~~ s2) -> (s2 ~~~ s1).
Proof.
  unfold bs_equivalent.
  intros H c c'.
  specialize (H c c').
  tauto.
Qed.

Ltac eq_by_2impl impl :=
  apply bs_2impl_eq; apply impl; try assumption; try (apply bs_eq_symm; assumption).

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
    split.
    - intro H. seq_inversion. seq_inversion. seq_apply.
    - intro H. seq_inversion. seq_inversion. seq_apply.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros c c'.
    split.
    - intro S. inversion_clear S. 
      + apply bs_If_True. assumption. seq_apply.
      + apply bs_If_False. assumption. apply bs_Skip.
    - intro H.
      inversion_clear H.
      + inversion_clear STEP. 
        apply bs_While_True with (c' := c'0) ; assumption.
      + assert (c' = (s0, i, o)). { inversion_clear STEP. reflexivity. }
        subst. apply bs_While_False. assumption.
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    dependent induction EXE.
    - specialize (IHEXE2 e s st i o). apply IHEXE2. reflexivity. reflexivity.
    - assumption.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. 
    unfold bs_equivalent.
    intros c c'.
    split.
    - intro W. destruct c'. destruct p. apply while_false in W.
      inversion_clear W.
    - intro I. inversion_clear I; inversion_clear CVAL.
  Qed.

  Lemma while_impl (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~> WHILE e DO s2 END.
  Proof.
    unfold bs_implies.
    unfold bs_equivalent in EQ.
    intros c c'.
    intro W. dependent induction W.
    - specialize (IHW2 e s1 EQ). apply bs_While_True with (c' := c').
        { assumption. } { apply EQ. assumption. } { apply IHW2. reflexivity. }
    - apply bs_While_False. assumption.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    eq_by_2impl while_impl.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. 
    unfold not.
    intro W. dependent induction W.
    - specialize (IHW2 s). apply IHW2. reflexivity.
    - inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent.
  unfold bs_equivalent in EQ.
  intros c c'.
  split.
  all: (intro H; seq_inversion; specialize (EQ c'0 c');
        apply EQ in STEP2; seq_apply).
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent.
  unfold bs_equivalent in EQ.
  intros c c'.
  split.
  all: (intro H; seq_inversion; specialize (EQ c c'0);
        apply EQ in STEP1; seq_apply).
Qed.

Lemma impl_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~> COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_implies.
  unfold bs_equivalent in EQ.
  intros c c'.
  intro H. inversion_clear H.
  - apply bs_If_True. assumption. assumption.
  - apply bs_If_False. assumption. apply EQ in STEP. assumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. 
  eq_by_2impl impl_congruence_cond_else.
Qed.

Lemma impl_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~> COND e THEN s2 ELSE s END.
Proof. 
  unfold bs_equivalent.
  unfold bs_equivalent in EQ.
  intros c c'.
  intro H. inversion_clear H.
  - apply bs_If_True. assumption. apply EQ in STEP. assumption.
  - apply bs_If_False. assumption. assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. 
  eq_by_2impl impl_congruence_cond_then.
Qed.

Lemma impl_congruence_while
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~> WHILE e DO s2 END.
Proof.
  unfold bs_equivalent.
  unfold bs_equivalent in EQ.
  intros c c'.
  intro W. dependent induction W.
  - specialize (IHW2 e s1 EQ). apply bs_While_True with (c' := c').
    { assumption. } { apply EQ. assumption. } { apply IHW2. reflexivity. }
  - apply bs_While_False. assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. 
  eq_by_2impl impl_congruence_while.
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
         apply eq_congruence_while; repeat assumption.
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
  generalize dependent c.
  generalize dependent c1.
  generalize dependent c2.
  induction s ; intros.

  - inversion EXEC1. inversion EXEC2. transitivity c; auto.

  - inversion EXEC1. inversion EXEC2. subst.
    inversion H6. subst.
    assert (z = z0). { apply (eval_deterministic e s); assumption. }
    subst. reflexivity.

  - inversion EXEC1. inversion EXEC2. 
    subst. inversion H4. reflexivity.

  - inversion EXEC1. inversion EXEC2. 
    subst. inversion H4. subst.
    assert (z = z0). { apply (eval_deterministic e s); assumption. }
    subst. reflexivity.

  - inversion_clear EXEC1. inversion_clear EXEC2.
    specialize (IHs1 c' c'0 c STEP0 STEP1). subst.
    specialize (IHs2 c1 c2 c' STEP3 STEP2). auto.
  
  - inversion EXEC1; inversion EXEC2; subst; inversion H8; subst.
    + specialize (IHs1 c2 c1 (s, i, o) STEP STEP0). auto.
    + eval_zero_not_one.
    + eval_zero_not_one.
    + specialize (IHs2 c2 c1 (s, i, o) STEP STEP0). auto.
  
  - dependent induction EXEC1.
    + clear IHEXEC1_1.
      specialize (IHEXEC1_2 s IHs e).
      apply IHEXEC1_2.
      * reflexivity.
      * assert (c'' = c2).
        { inversion_clear EXEC2.
          - apply IHEXEC1_2. reflexivity.
            assert (c'0 = c'). { apply (IHs c' c'0 (st, i, o)); assumption. }
            subst. assumption.
          - eval_zero_not_one. }
        subst. assumption.
    + inversion_clear EXEC2.
      * eval_zero_not_one.
      * reflexivity.
Qed.

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
  forall (C : Context), (C <~ s1) ~~~ (C <~ s2).
Notation "s1 '~c~' s2" := (contextual_equivalent s1 s2)
                            (at level 42, no associativity).

(* Contextual equivalence is equivalent to the semantic one *)
(* TODO: no longer needed *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); assumption.
    
Lemma eq_eq_ceq s1 s2: s1 ~~~ s2 <-> s1 ~c~ s2.
Proof.
  unfold bs_equivalent.
  unfold contextual_equivalent.
  split.
  - intro H.
    induction C; simpl; auto.
    + apply eq_congruence. exact (Nat 42). assumption.
    + apply eq_congruence. exact (Nat 37). assumption.
    + apply eq_congruence. assumption.
    + apply eq_congruence. assumption.
    + apply eq_congruence. exact SKIP. assumption.
  - intros H c c'. 
    specialize (H Hole). simpl in H.
    apply H.
Qed.

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
    generalize dependent c.
    generalize dependent c'.
    generalize dependent c''.
    induction s; intros.

    - inversion_clear EXEC1. inversion_clear EXEC2. reflexivity.

    - inversion EXEC1. inversion EXEC2. subst. inversion H6. subst.
      assert (z = z0). { apply (eval_deterministic e s); assumption. }
      subst. reflexivity.

    - inversion EXEC1. inversion EXEC2. subst. inversion H4. subst. reflexivity.

    - inversion EXEC1. inversion EXEC2. subst. inversion H4. subst.
      assert (z = z0). { apply (eval_deterministic e s); assumption. }
      subst. reflexivity.

    - inversion_clear EXEC1; inversion_clear EXEC2.
      + specialize (IHs1 (None, c'0) (None, c'1) c SSTEP0 SSTEP).
        inversion IHs1. reflexivity.
      + specialize (IHs1 (None, c'0) (Some s1', c'1) c SSTEP0 SSTEP).
        inversion IHs1.
      + specialize (IHs1 (Some s1', c'0) (None, c'1) c SSTEP0 SSTEP).
        inversion IHs1.
      + specialize (IHs1 (Some s1', c'0) (Some s1'0, c'1) c SSTEP0 SSTEP).
        inversion IHs1. reflexivity.
    
    - inversion EXEC1; inversion EXEC2; subst; inversion H8; subst.
      all: try reflexivity. all: try eval_zero_not_one.
  
    - inversion_clear EXEC1. inversion_clear EXEC2. reflexivity.
Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof. 
    induction STEP1; inversion_clear STEP2.
    - remember (ss_int_step_deterministic s c (None, c') (None, c'') H H0) as P.
      inversion P. reflexivity.
    - remember (ss_int_step_deterministic s c (None, c') (Some s', c'0) H H0) as P.
      inversion P.
    - remember (ss_int_step_deterministic s c (Some s', c') (None, c'') H H0) as P.
      inversion P.
    - remember (ss_int_step_deterministic s c (Some s', c') (Some s'0, c'0) H H0) as P.
      inversion P. subst. apply IHSTEP1. assumption.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. 
    induction s; inversion STEP.
    - apply bs_Skip.
    - subst. apply bs_Assign. assumption.
    - subst. apply bs_Read.
    - subst. apply bs_Write. assumption.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof. 
    induction STEP1.
    - apply ss_int_Step with (c' := c'0) (s' := s2). 
      + constructor. assumption.
      + assumption.
    - apply ss_int_Step with (c' := c'0) (s' := (s' ;; s2)). 
      + apply (ss_Seq_InCompl). assumption.
      + apply IHSTEP1. assumption.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent s'.
    generalize dependent c'.
    generalize dependent c''.
    induction s; intros; inversion STEP; subst.
    - apply bs_Seq with (c' := c').
      + apply ss_bs_base. assumption.
      + assumption.
    - inversion_clear EXEC.
      apply bs_Seq with (c' := c'0).
      + specialize (IHs1 c'0 c' s1' SSTEP STEP1). assumption.
      + assumption.
    - apply bs_If_True; try assumption.
    - apply bs_If_False; try assumption.
    - apply SmokeTest.while_unfolds. assumption.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split.
    - intro H. 
      generalize dependent c. 
      generalize dependent c'. 
      induction s; intros.
      + inversion_clear H. constructor. apply ss_Skip.
      + inversion_clear H. constructor. apply ss_Assign. assumption.
      + inversion_clear H. constructor. apply ss_Read.
      + inversion_clear H. constructor. apply ss_Write. assumption.
      + inversion_clear H.
        specialize (IHs1 c'0 c STEP1). specialize (IHs2 c' c'0 STEP2).
        apply ss_ss_composition with (c'' := c'0); assumption.
      + inversion_clear H.
        * apply ss_int_Step with (s' := s1) (c' := (s, i, o)).
          { apply ss_If_True. assumption. }
          { apply IHs1. assumption. }
        * apply ss_int_Step with (s' := s2) (c' := (s, i, o)).
          { apply ss_If_False. assumption. }
          { apply IHs2. assumption. }
      + inversion_clear H.
        * generalize dependent o.
          generalize dependent i.
          generalize dependent st.
          dependent induction WSTEP; intros.
          { clear IHWSTEP1.
            assert (WHILE e DO s END = WHILE e DO s END) as TEQ. { reflexivity. }
            specialize (IHWSTEP2 s IHs e TEQ st CVAL i o WSTEP1).
            apply ss_int_Step with (s' := (COND e THEN s ;; WHILE e DO s END ELSE SKIP END)) (c' := (st0, i0, o0)).
            apply ss_While.
            apply ss_int_Step with (s' := s;; (WHILE e DO s END)) (c' := (st0, i0, o0)).
            - apply ss_If_True. assumption.
            - apply ss_ss_composition with (c'' := (st, i, o)).
              + apply IHs. assumption.
              + assumption. }
          { apply ss_int_Step with (s' := (COND e THEN s ;; WHILE e DO s END ELSE SKIP END)) (c' := (st0, i0, o0)).
            apply ss_While.
            apply ss_int_Step with (s' := (s ;; WHILE e DO s END)) (c' := (st0, i0, o0)).
            - apply ss_If_True. assumption.
            - apply ss_ss_composition with (c'' := (st, i, o)).
              + apply IHs. assumption.
              + apply ss_int_Step with (s' := (COND e THEN s ;; WHILE e DO s END ELSE SKIP END)) (c' := (st, i, o)).
                apply ss_While.
                apply ss_int_Step with (s' := (SKIP)) (c' := (st, i, o)).
                * apply ss_If_False. assumption.
                * constructor. constructor. }
        * apply ss_int_Step with (s' := (COND e THEN s ;; WHILE e DO s END ELSE SKIP END)) (c' := (st, i, o)).
          { apply ss_While. }
          { apply ss_int_Step with (s' := SKIP) (c' := (st, i, o)).
            - apply ss_If_False. assumption.
            - constructor. constructor. }
    - intro H.
      induction H.
      + apply ss_bs_base. assumption.
      + apply ss_bs_step with (s' := s') (c' := c'); assumption.
  Qed.
  
End SmallStep.

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
