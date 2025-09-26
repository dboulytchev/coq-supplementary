Require Import List.
Import ListNotations.
Require Import Lia.

Require Import Stdlib.Program.Equality.
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
  apply (H Hole).
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists (Id 11 ::= Nat 44), (Id 22 ::= Nat 66).
  split.
  - unfold eval_equivalent; intros; split; intros;
    inversion H; inversion H0; repeat econstructor.
  - intro H.
    specialize (H (SeqL (Hole) (WRITE (Var (Id 11))))).
    specialize (H ([]) ([44%Z])).
    destruct H as [H _].
    specialize (H ltac:(repeat econstructor)).
    inversion H.
    subst.
    inversion H0.
    subst.
    inversion STEP1.
    subst.
    inversion STEP2.
    subst.
    inversion VAL.
    subst.
    inversion VAL0.
    subst.
    inversion VAR.
    subst.
    inversion H7.
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
    split;
    intros.
    all: repeat(seq_inversion);
         repeat(seq_apply).
  Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    split; intros.


    - inversion H; subst.
      + constructor. assumption. seq_apply.
      + apply bs_If_False. assumption. constructor.
    - inversion H; subst; inversion STEP; subst.
      + econstructor.
        { assumption. }
        { eauto. }
        { auto. }
      + apply bs_While_False. assumption.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    dependent induction EXE;
    eauto.
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent; split; intros.
    - inversion_clear H.
      + inversion STEP.
        destruct c', p.
        apply (while_false (Nat 1) SKIP s l0 l c'0) in WSTEP.
        inversion WSTEP.
      + inversion CVAL.
    - inversion_clear H.
      all: inversion STEP;
           destruct c', p;
           apply bs_While_False;
           inversion CVAL.
  Qed.
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    split; intro.
    - dependent induction H.
        + apply (bs_While_True _ _ _ c').
          * auto.
          * apply EQ.
            auto.
          * apply (IHbs_int2 e) in EQ.
          all: auto.
        + intuition.
    - dependent induction H.
        + apply (bs_While_True _ _ _ c').
          * intuition.
          * apply EQ.
            auto.
          * apply (IHbs_int2 e) in EQ.
            all: auto.
        + intuition.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro.
    dependent induction H.
      - eauto.
      - inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  split;
  intro;
  dependent induction H;
  apply (bs_Seq c c' c'');
  intuition;
  apply EQ;
  intuition.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  split;
  intro;
  dependent induction H;
  apply (bs_Seq c c' c'');
  intuition;
  apply EQ;
  intuition.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent.
  intros.
  split; intro H; inversion_clear H;
  try (apply bs_If_False; eauto; apply EQ; eauto); eauto.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent.
  intros.
  split; intro H; inversion_clear H;
  try (apply bs_If_True; eauto; apply EQ; eauto); eauto.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  apply SmokeTest.while_eq.
  intuition.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split.
  apply eq_congruence_seq_r.
  intuition.
  split.
  apply eq_congruence_seq_l.
  intuition.
  split.
  apply eq_congruence_cond_else.
  intuition.
  split.
  apply eq_congruence_cond_then.
  intuition.
  apply eq_congruence_while.
  intuition.
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
  dependent induction EXEC1 in c2;
  dependent destruction EXEC2;
  try auto; try by_eval_deterministic;
  try eval_zero_not_one.
    - apply IHEXEC1_2.
      apply (IHEXEC1_1 c'0) in EXEC2_1.
      rewrite <- EXEC2_1 in EXEC2_2.
      intuition.
    - apply IHEXEC1_2.
      apply (IHEXEC1_1 c'0) in EXEC2_1.
      rewrite EXEC2_1.
      intuition.
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
    dependent induction STEP1;
    dependent destruction STEP2;

    remember (ss_int_step_deterministic _ _ _ _ H H0);
    inversion e;
    intuition.
    apply IHSTEP1.
    rewrite H2, H3.
    trivial.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    dependent induction STEP.
      - apply bs_Skip.
      - apply bs_Assign. intuition.
      - apply bs_Read.
      - apply bs_Write. intuition.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    generalize dependent c'. induction STEP1; intros.
    - apply (ss_int_Step _ s2 _ c').
      constructor.
      auto.
      auto.
    - apply (ss_int_Step _ (s' ;; s2) _ c').
      constructor.
      auto.
      apply IHSTEP1.
      auto.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    dependent induction s generalizing c c' c'';
    dependent destruction STEP.
    - apply bs_Seq with (c' := c'). 
        + apply ss_bs_base.
          auto.
        + auto.
    - dependent destruction EXEC.
      apply bs_Seq with(c' := c').
        + apply (IHs1 _ _ _ _ STEP).
          auto.
        + auto.
    - apply bs_If_True.
      all: auto.
    - apply bs_If_False.
      all: auto.
    - apply SmokeTest.while_unfolds.
      auto.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split.
  - intros. induction H.
    + apply ss_int_Base.
      apply ss_Skip.
    + apply ss_int_Base.
      apply ss_Assign.
      assumption.
    + apply ss_int_Base.
      apply ss_Read.
    + apply ss_int_Base.
      apply ss_Write.
      assumption.
    + apply ss_ss_composition with c'.
      * assumption.
      * assumption.
    + eapply ss_int_Step.
      * apply ss_If_True. 
        assumption.
      * assumption.
    + eapply ss_int_Step.
      * apply ss_If_False. 
        assumption.
      * assumption.
    + eapply ss_int_Step.
      * apply ss_While.
      * eapply ss_int_Step.
        -- apply ss_If_True. 
           assumption.
        -- apply ss_ss_composition with c'.
           ++ assumption.
           ++ assumption.
    + eapply ss_int_Step.
      * apply ss_While.
      * eapply ss_int_Step.
        -- apply ss_If_False. 
           assumption.
        -- apply ss_int_Base. 
           apply ss_Skip.
  - intros. induction H.
    + apply ss_bs_base. assumption.
    + eapply ss_bs_step. 
      * exact H.
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
    dependent induction s; simpl; try rewrite Renaming.re_rename_expr; congruence.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    dependent destruction r. 
    constructor. 
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
    dependent induction Hbs;
    simpl.
    eapply bs_Skip.
    eapply bs_Assign.
    rewrite <- Renaming.eval_renaming_invariance; auto.
    eapply bs_Read.
    eapply bs_Write.
    rewrite <- Renaming.eval_renaming_invariance; auto.
    eapply bs_Seq; eauto.
    eapply bs_If_True; eauto.
    rewrite <- Renaming.eval_renaming_invariance; auto.
    eapply bs_If_False; eauto.
    rewrite <- Renaming.eval_renaming_invariance; auto.
    eapply bs_While_True; eauto.
    rewrite <- Renaming.eval_renaming_invariance; auto.
    eapply bs_While_False; eauto.
    rewrite <- Renaming.eval_renaming_invariance; auto.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    specialize (Renaming.renaming_inv r) as [r_inv Hinv].
    apply (renaming_invariant_bs _ r_inv) in Hbs.
    rewrite (re_rename r_inv r) in Hbs.
    - destruct c as [[st i] o], c' as [[st' i'] o']; simpl in Hbs.
      rewrite !Renaming.re_rename_state in Hbs; auto.
    - assumption.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    split; intros [].
    - eexists. 
      eapply renaming_invariant_bs in H. 
      eauto.
    - specialize (Renaming.renaming_inv r) as [r' Hrr'].
      eexists.
      replace s with (rename r' (rename r s)).
      + eapply renaming_invariant_bs in H; eauto.
      + rewrite (re_rename r' r); eauto using Renaming.re_rename.
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
  induction EXEC; intros S Hdef; subst.
  - discriminate.
  - cps_bs_gen_helper k Hdef bs_Skip.
  - cps_bs_gen_helper k Hdef bs_Assign.
  - cps_bs_gen_helper k Hdef bs_Read.
  - cps_bs_gen_helper k Hdef bs_Write.
  - destruct k eqn:K; subst; inversion Hdef; subst.
    + apply IHEXEC; auto.
    + apply SmokeTest.seq_assoc; apply IHEXEC; auto.
  - destruct k eqn:K; subst; inversion Hdef; subst.
    + apply bs_If_True; auto; apply IHEXEC; auto.
    + assert (H : (s, i, o) == s1;; s0 ==> c') by (apply IHEXEC; auto).
      inversion H; subst.
      apply (bs_Seq _ c'0).
      * apply bs_If_True; auto; assumption.
      * assumption.
  - destruct k eqn:K; subst; inversion Hdef; subst.
    + apply bs_If_False; auto; apply IHEXEC; auto.
    + assert (H : (s, i, o) == s2;; s0 ==> c') by (apply IHEXEC; auto).
      inversion H; subst.
      apply (bs_Seq _ c'0).
      * apply bs_If_False; auto; assumption.
      * assumption.
  - destruct k eqn:K; subst; inversion Hdef; subst.
    + apply SmokeTest.while_unfolds; apply bs_If_True; auto; apply IHEXEC; auto.
    + assert (H: ((st, i, o)) == s;; (WHILE e DO s END);; s0 ==> c' ->
                    ((st, i, o)) == (WHILE e DO s END);; s0 ==> c').
      { intros Hseq. inversion Hseq; subst. inversion STEP2; subst.
        apply (bs_Seq _ c'1).
        - apply SmokeTest.while_unfolds; apply bs_If_True; auto.
          apply (bs_Seq _ c'0); assumption.
        - assumption. }
      apply H; apply IHEXEC; auto.
  - destruct k eqn:K; subst; inversion Hdef; subst.
    + inversion EXEC; subst; apply bs_While_False; auto.
    + apply (bs_Seq _ (st, i, o)).
      * apply bs_While_False; auto.
      * apply IHEXEC; auto.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  apply cps_bs_gen with (k := !s2) (S1:= !s1); eauto.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
  apply cps_bs_gen with (S1 := !s) (k := KEmpty); eauto.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1;
  destruct k2;
  unfold Kapp;
  try(econstructor);
  eauto;
  destruct k3;
  unfold Kapp in STEP;
  inversion STEP.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. 
  inversion_clear STEP;
  generalize dependent k.
  generalize c3.
  dependent induction EXEC; intros.
  - apply cps_Skip; auto.
  - apply cps_Assign with (n := z); auto.
  - apply cps_Read; auto.
  - apply cps_Write with (z := z); auto.
  - apply cps_Seq.
    apply IHEXEC1.
    destruct k.
    + apply IHEXEC2.
      auto.
    + apply cps_Seq.
      apply IHEXEC2.
      auto.
  - apply cps_If_True; auto.
  - apply cps_If_False; auto.
  - apply cps_While_True.
    + auto.
    + apply IHEXEC1.
       destruct k; try (apply cps_Seq); apply IHEXEC2; auto.
  - apply cps_While_False; auto.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  apply bs_int_to_cps_int_cont with (c2 := c'). 
   - auto. 
   - apply cps_Skip.
     apply cps_Empty.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
