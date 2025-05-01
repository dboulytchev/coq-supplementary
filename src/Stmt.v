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
Proof. 
  unfold contextual_equivalent in H.
  apply (H Hole).
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. admit. Admitted.

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
    constructor; intros.
    - inversion H.
      inversion STEP1.
      remember (bs_Seq c'1 c'0 c' s2 s3 STEP3 STEP2).
      apply (bs_Seq c c'1 c' s1 (s2 ;; s3) STEP0 b).
    - inversion H.
      inversion STEP2.
      remember (bs_Seq c c'0 c'1 s1 s2 STEP1 STEP0).
      apply (bs_Seq c c'1 c' (s1 ;; s2) s3 b STEP3).
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. 
    unfold bs_equivalent.
    intros.
    split.
    - intro.
      inversion H.
      + apply bs_If_True.
        * trivial.
        * econstructor.
          -- eauto.
          -- trivial.
      + apply bs_If_False.
        * trivial.
        * constructor.
    - intro.
      inversion H. inversion STEP.
      econstructor.
      + trivial.
      + eauto.
      + eauto.
      + destruct c'.
        destruct p.
        inversion STEP.
        apply bs_While_False.
        subst.
        exact CVAL.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof. 
    dependent induction EXE.
    - remember (IHEXE2 e s st i o). auto.
    - trivial.
  Qed.
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. 
    intro.
    constructor.
    - intro. dependent induction H.
      + intuition. inversion H. rewrite <- H4 in H1. auto.
      + inversion CVAL.
    - intro.
      dependent induction H; inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof. 
    unfold "~~~".
    intros. split.
    - intros.
      dependent induction H.
      eapply bs_While_True. 
      + trivial.
      + apply EQ. eassumption.
      + eapply IHbs_int2; eauto.
      + eapply bs_While_False. eassumption.
    - intros. dependent induction H.
      eapply bs_While_True.
      + eassumption.
      + apply EQ. eassumption.
      + eapply IHbs_int2; eauto.
      + eapply bs_While_False. assumption.
  Qed.
      
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. 
    unfold not. intros.
    remember (WHILE Nat 1 DO s END) in H.
    induction H; inversion Heqs0; subst.
    - apply IHbs_int2. trivial.
    - inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof. 
  unfold bs_equivalent. unfold bs_equivalent in EQ.
  intros c c'. 
  split; intro; seq_inversion; 
  specialize (EQ c'0 c'); apply EQ in STEP2; seq_apply.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent. unfold bs_equivalent in EQ.
  intros.
  split; intro; seq_inversion; 
  specialize (EQ c  c'0); apply EQ in STEP1; seq_apply.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. 
  unfold bs_equivalent.
  intros.
  split; intros; inversion H; subst.
  - apply bs_If_True; trivial.
  - apply bs_If_False.
    + auto.
    + apply EQ. trivial.
  - apply bs_If_True; trivial.
  - apply bs_If_False.
    + auto.
    + apply EQ. trivial.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. 
  unfold bs_equivalent.
  intros.
  split; intros; inversion H; subst.
  - apply bs_If_True.
    + auto.
    + apply EQ. trivial.
  - apply bs_If_False; trivial.
  - apply bs_If_True.
    + auto.
    + apply EQ. trivial.
  - apply bs_If_False; trivial.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. 
  unfold bs_equivalent.
  intros.
  split; intros; dependent induction H.
  - eapply bs_While_True.
    + assumption.
    + apply EQ. eassumption.
    + eapply IHbs_int2.
      * eauto.
      * trivial.
  - apply bs_While_False; trivial.
  - eapply bs_While_True.
    + auto.
    + apply EQ in H. eauto.
    + eauto.
  - apply bs_While_False; trivial.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split.
  - apply eq_congruence_seq_r. trivial.
  - split.
    + apply eq_congruence_seq_l. trivial.
    + split.
      * apply eq_congruence_cond_else. trivial.
      * split. 
        -- apply eq_congruence_cond_then. trivial.
        -- apply eq_congruence_while. trivial.
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
  induction EXEC1; intros; inversion EXEC2.
  - trivial.
  - apply (eval_deterministic e s z z0) in VAL.
    + subst z. trivial.
    + trivial.
  - auto.
  - apply (eval_deterministic e s z z0) in VAL.
    + subst z. trivial.
    + trivial.
  - apply IHEXEC1_1 in STEP1. subst c'0. apply IHEXEC1_2 in STEP2. trivial.
  - auto.
  - eval_zero_not_one.
  - eval_zero_not_one.
  - auto.
  - apply IHEXEC1_1 in STEP. subst c'0. apply IHEXEC1_2 in WSTEP. trivial.
  - eval_zero_not_one.
  - eval_zero_not_one.
  - trivial.
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
  Proof. generalize dependent c''. induction EXEC1; intros; inversion EXEC2.
    - trivial.
    - assert (z = z0). 
      + apply eval_deterministic with e s.
        * exact SVAL. 
        * exact SVAL0.
      + subst. trivial.
    - trivial.
    - assert (z = z0). 
      + apply eval_deterministic with e s. 
        * exact SVAL.
        * exact SVAL0. 
      + subst. trivial.
    - assert ((None : (option stmt), c') = (None, c'0)). 
      + apply IHEXEC1. exact SSTEP.
      + inversion H. subst. trivial.
    - assert ((None, c') = (Some s1', c'0)). 
      + apply IHEXEC1. exact SSTEP.
      + inversion H.
    - assert ((Some s1', c') = (None, c'0)).
      + apply IHEXEC1. exact SSTEP.
      + inversion H.
    - assert ((Some s1', c') = (Some s1'0, c'0)). 
      + apply IHEXEC1. exact SSTEP.
      + inversion H. subst. trivial.
    - trivial.
    - assert (Z.zero = Z.one). 
      + apply eval_deterministic with e s. 
        * exact SCVAL0. 
        * exact SCVAL.
      + inversion H6.
    - assert (Z.zero = Z.one). 
      + apply eval_deterministic with e s. 
        * exact SCVAL.
        * exact SCVAL0.
      + inversion H6.
    - trivial.
    - trivial.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof. 
    generalize dependent c''.
    induction STEP1.
    - intros. inversion STEP2.
      + apply ss_int_step_deterministic with (c' := (None, c'')) in H.
        * inversion H. trivial.
        * trivial.
      + apply ss_int_step_deterministic with (c' := (Some s', c'0)) in H.
        inversion H. trivial.
    - intros. inversion STEP2.
      + apply ss_int_step_deterministic with (c' := (None, c''0)) in H.
        * inversion H.
        * trivial.
      + apply ss_int_step_deterministic with (c' := (Some s'0, c'0)) in H.
        * inversion H. subst. apply IHSTEP1. trivial.
        * trivial.
  Qed.

  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. 
    induction s; intros; inversion STEP; subst.
    - apply bs_Skip.
    - apply bs_Assign. trivial.
    - apply bs_Read.
    - apply bs_Write. trivial.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    generalize dependent c'.
    induction STEP1; intros.
    - apply ss_int_Step with (s2) (c').
      apply ss_Seq_Compl. 
      + trivial.
      + trivial.
    - apply ss_int_Step with (s' ;; s2) (c').
      apply ss_Seq_InCompl. 
      + trivial.
      + apply IHSTEP1 in STEP2. trivial.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.  generalize dependent EXEC.
    generalize dependent STEP.
    generalize dependent c''.
    generalize dependent c'.
    generalize dependent c.
    generalize dependent s'.
    induction s; intros; inversion STEP.
    - apply ss_bs_base in SSTEP. seq_apply.
    - subst s'. inversion EXEC. subst.
      apply IHs1 with (c'':=c'1) in SSTEP. 
      + seq_apply.
      + trivial.
    - apply bs_If_True. 
      + trivial.
      + subst. trivial.
    - apply bs_If_False.
      + trivial.
      + subst. trivial.
    - inversion STEP.
      subst s'. inversion EXEC; subst.
      + inversion STEP0. subst.
        apply bs_While_True with (c').
        * trivial.
        * trivial.
        * trivial.
      + inversion STEP0.
        apply bs_While_False. trivial.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. 
    split; intro. (* oh. *)
    - induction H.
      + apply ss_int_Base. apply ss_Skip.
      + apply ss_int_Base. apply ss_Assign. exact VAL.
      + apply ss_int_Base. apply ss_Read.
      + apply ss_int_Base. apply ss_Write. exact VAL.
      + apply ss_ss_composition with c'. 
        * trivial.
        * trivial.
      + apply ss_int_Step with s1 (s, i, o). 
        * apply ss_If_True. trivial.
        * trivial.
      + apply ss_int_Step with s2 (s, i, o). 
        * apply ss_If_False. trivial.
        * trivial.
      + apply ss_int_Step with (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (st, i, o). 
        * apply ss_While.
        * apply ss_int_Step with (s ;; WHILE e DO s END) (st, i, o). 
          -- apply ss_If_True. trivial.
          -- apply ss_ss_composition with c'; trivial. 
      + apply ss_int_Step with (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (st, i, o). 
        * apply ss_While.
        * apply ss_int_Step with SKIP (st, i, o). 
          -- apply ss_If_False. trivial.
          -- apply ss_int_Base. apply ss_Skip.
    - induction H.
      + apply ss_bs_base. trivial.
      + apply ss_bs_step with c' s'; trivial. 
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
    simpl. unfold Renaming.rename_state.
    destruct r. trivial. (* I like when enormous match is 'trivial'. Good thing. *)
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    dependent destruction r.
    dependent destruction b.
    dependent induction Hbs; simpl.
    - eapply bs_Skip.
    - eapply bs_Assign. rewrite <- Renaming.eval_renaming_invariance. trivial.
    - eapply bs_Read.
    - eapply bs_Write. rewrite <- Renaming.eval_renaming_invariance. trivial.
    - eapply bs_Seq; eauto.
    - eapply bs_If_True; eauto. rewrite <- Renaming.eval_renaming_invariance. trivial.
    - eapply bs_If_False; eauto. rewrite <- Renaming.eval_renaming_invariance. trivial.
    - eapply bs_While_True; eauto. rewrite <- Renaming.eval_renaming_invariance. trivial.
    - eapply bs_While_False; eauto. rewrite <- Renaming.eval_renaming_invariance. trivial.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    remember (Renaming.renaming_inv r). 
    inversion e.
    apply renaming_invariant_bs with (r:=x) in Hbs.
    rewrite re_rename in Hbs. 
    unfold rename_conf in Hbs.
    - destruct c, c', p, p0. do 2 rewrite Renaming.re_rename_state in Hbs; trivial.
    - trivial.
  Qed.

    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent.
    unfold eval. split; intros.
      - destruct H.
       apply renaming_invariant_bs with (r:=r) in H.
       simpl in H. exists (Renaming.rename_state r x). trivial.
      - destruct H. remember (Renaming.renaming_inv2 r) as H1.
       inversion H1. 
       rewrite <- (Renaming.re_rename_state r x0 H0 ([])) in H.
       rewrite <- (Renaming.re_rename_state r x0 H0 x) in H.
       apply (
          renaming_invariant_bs_inv 
          s 
          r 
          ((Renaming.rename_state x0 ([])), i, []) 
          ((Renaming.rename_state x0 x), [], o)) in H.
       simpl in H.
       exists (Renaming.rename_state x0 x). trivial.
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
