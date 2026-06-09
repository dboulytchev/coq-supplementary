Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Coq.Program.Equality.

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
  exact (H Hole).
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists (Id 0 ::= Nat 1), (Id 0 ::= Nat 2).
  split.
  - unfold eval_equivalent, eval. intros i o. split; intros [st H];
      inversion H; subst; eexists; constructor; constructor.
  - intros HC.
    specialize (HC (SeqL Hole (WRITE (Var (Id 0)))) nil (1%Z :: nil)).
    simpl in HC. destruct HC as [HC _].
    assert (<| (Id 0 ::= Nat 1) ;; WRITE (Var (Id 0)) |> nil => (1%Z :: nil)).
    { unfold eval. eexists.
      eapply bs_Seq.
      - constructor. constructor.
      - constructor. constructor. constructor.
    }
    specialize (HC H). clear H.
    unfold eval in HC. destruct HC as [st H].
    repeat match goal with
           | H : _ == _ ==> _ |- _ => inversion H; subst; clear H
           | H : [| _ |] _ => _ |- _ => inversion H; subst; clear H
           | H : _ / _ => _ |- _ => inversion H; subst; clear H
           end; congruence.
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
    unfold bs_equivalent. split; intros H; repeat seq_inversion; seq_apply.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent. split; intros H.
    - inversion H; subst.
      + apply bs_If_True; auto. eapply bs_Seq; eauto.
      + apply bs_If_False; auto.
    - inversion H; subst.
      + inversion STEP; subst. eapply bs_While_True; eauto.
      + inversion STEP; subst. apply bs_While_False; auto.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as loop.
    remember (st, i, o) as cf.
    induction EXE; inversion Heqloop; subst.
    - eapply IHEXE2; eauto.
    - inversion Heqcf; subst. assumption.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent. split; intros H.
    - inversion H; subst.
      + destruct c' as [[st' i'] o'].
        pose proof (while_false (Nat 1) SKIP st' i' o' _ WSTEP) as HF.
        inversion HF.
      + inversion CVAL.
    - inversion H; subst; inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent in *. split; intro H.
    - remember (WHILE e DO s1 END) as loop.
      induction H; inversion Heqloop; subst.
      + eapply bs_While_True; eauto. apply EQ; eauto.
      + apply bs_While_False; auto.
    - remember (WHILE e DO s2 END) as loop.
      induction H; inversion Heqloop; subst.
      + eapply bs_While_True; eauto. apply EQ; eauto.
      + apply bs_While_False; auto.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro H.
    remember (WHILE Nat 1 DO s END) as loop.
    induction H; inversion Heqloop; subst.
    - eauto.
    - inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent in *. split; intros H; inversion H; subst;
    eapply bs_Seq; eauto; apply EQ; eauto.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent in *. split; intros H; inversion H; subst;
    eapply bs_Seq; eauto; apply EQ; eauto.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent in *. split; intros H; inversion H; subst.
  - apply bs_If_True; auto.
  - apply bs_If_False; auto. apply EQ; auto.
  - apply bs_If_True; auto.
  - apply bs_If_False; auto. apply EQ; auto.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent in *. split; intros H; inversion H; subst.
  - apply bs_If_True; auto. apply EQ; auto.
  - apply bs_If_False; auto.
  - apply bs_If_True; auto. apply EQ; auto.
  - apply bs_If_False; auto.
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
  split.
  - apply eq_congruence_seq_r. assumption.
  - split.
    + apply eq_congruence_seq_l. assumption.
    + split.
      * apply eq_congruence_cond_else. assumption.
      * split.
        -- apply eq_congruence_cond_then. assumption.
        -- apply eq_congruence_while. assumption.
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
  dependent induction EXEC1 in c2; dependent destruction EXEC2;
    try auto; try by_eval_deterministic; try eval_zero_not_one.
  - apply IHEXEC1_2.
    apply IHEXEC1_1 in EXEC2_1. rewrite <- EXEC2_1 in EXEC2_2.
    assumption.
  - apply IHEXEC1_2.
    apply IHEXEC1_1 in EXEC2_1. rewrite EXEC2_1.
    assumption.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma equivalent_states_update (s1 s2 : state Z) (x : id) (n : Z)
      (HEQ : equivalent_states s1 s2) :
  equivalent_states (s1 [x <- n]) (s2 [x <- n]).
Proof.
  unfold equivalent_states, Expr.equivalent_states in *.
  intros y z. destruct (id_eq_dec x y) as [EQ | NEQ].
  - subst. split; intros H; inversion H; subst; try contradiction; constructor.
  - split; intros H.
    + apply update_neq; auto. apply HEQ. apply update_neq in H; auto.
    + apply update_neq; auto. apply HEQ. apply update_neq in H; auto.
Qed.

Lemma eval_equivalent_states (e : expr) (s1 s2 : state Z) (z : Z)
      (HEQ : equivalent_states s1 s2)
      (EVAL : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
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
  remember (st1, i, o) as c1.
  remember (st2, i', o') as c2.
  revert st1 st1' st2 i o i' o' HE1 Heqc1 Heqc2.
  induction H; intros; inversion Heqc1; inversion Heqc2; subst;
    repeat match goal with
           | H : (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
           end.
  - exists st1'. split.
    + unfold equivalent_states, Expr.equivalent_states in *.
      intros id0 z0. apply HE1.
    + constructor.
  - exists (st1' [x <- z]). split.
    + apply equivalent_states_update. assumption.
    + constructor. eapply eval_equivalent_states; eauto.
  - exists (st1' [x <- z]). split.
    + apply equivalent_states_update. assumption.
    + constructor.
  - exists st1'. split; auto. constructor. eapply eval_equivalent_states; eauto.
  - destruct c' as [[stm im] om].
    edestruct IHbs_int1 as [stm' [HEM EXECM]]; eauto.
    edestruct IHbs_int2 as [st2' [HE2 EXEC2]]; eauto.
  - edestruct IHbs_int as [st2' [HE2 EXEC]]; eauto.
    exists st2'. split; auto.
    apply bs_If_True; auto. eapply eval_equivalent_states; eauto.
  - edestruct IHbs_int as [st2' [HE2 EXEC]]; eauto.
    exists st2'. split; auto.
    apply bs_If_False; auto. eapply eval_equivalent_states; eauto.
  - destruct c' as [[stm im] om].
    edestruct IHbs_int1 as [stm' [HEM EXECM]]; eauto.
    edestruct IHbs_int2 as [st2' [HE2 EXEC2]]; eauto.
    exists st2'. split; auto.
    eapply bs_While_True; eauto. eapply eval_equivalent_states; eauto.
  - exists st1'. split; auto.
    apply bs_While_False. eapply eval_equivalent_states; eauto.
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
    generalize dependent c''.
    induction EXEC1; intros c'' EXEC2; inversion EXEC2; subst; auto;
      try by_eval_deterministic; try eval_zero_not_one.
    - apply IHEXEC1 in SSTEP. inversion SSTEP. reflexivity.
    - apply IHEXEC1 in SSTEP. inversion SSTEP.
    - apply IHEXEC1 in SSTEP. inversion SSTEP.
    - apply IHEXEC1 in SSTEP. inversion SSTEP. reflexivity.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''.
    induction STEP1; intros c2 STEP2; inversion STEP2; subst; auto.
    - pose proof (ss_int_step_deterministic _ _ _ _ H H0) as HH.
      inversion HH. reflexivity.
    - pose proof (ss_int_step_deterministic _ _ _ _ H H0) as HH.
      inversion HH.
    - pose proof (ss_int_step_deterministic _ _ _ _ H H0) as HH.
      inversion HH.
    - pose proof (ss_int_step_deterministic _ _ _ _ H H0) as HH.
      inversion HH; subst. apply IHSTEP1. assumption.
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
    induction STEP1.
    - eapply ss_int_Step.
      + apply ss_Seq_Compl. eassumption.
      + eassumption.
    - eapply ss_int_Step.
      + apply ss_Seq_InCompl. eassumption.
      + apply IHSTEP1. assumption.
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
    induction s; intros c'' c' c s' STEP EXEC; inversion STEP; subst.
    - eapply bs_Seq.
      + apply ss_bs_base. eassumption.
      + assumption.
    - inversion EXEC; subst.
      eapply bs_Seq.
      + eapply IHs1; eauto.
      + assumption.
    - apply bs_If_True; assumption.
    - apply bs_If_False; assumption.
    - apply SmokeTest.while_unfolds. assumption.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intro H.
    - induction H.
      + constructor. constructor.
      + constructor. constructor. assumption.
      + constructor. constructor.
      + constructor. constructor. assumption.
      + eapply ss_ss_composition; eauto.
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
          -- eapply ss_ss_composition; eauto.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_False. assumption.
          -- constructor. constructor.
    - induction H.
      + apply ss_bs_base. assumption.
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
    induction s; simpl; try rewrite Renaming.re_rename_expr; try rewrite Hinv;
      try rewrite IHs; try rewrite IHs1; try rewrite IHs2; auto.
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
    destruct r as [f Hf].
    induction Hbs; simpl.
    - constructor.
    - apply bs_Assign. apply Renaming.eval_renaming_invariance. assumption.
    - apply bs_Read.
    - constructor. apply Renaming.eval_renaming_invariance. assumption.
    - eapply bs_Seq; eauto.
    - apply bs_If_True.
      + apply Renaming.eval_renaming_invariance. assumption.
      + assumption.
    - apply bs_If_False.
      + apply Renaming.eval_renaming_invariance. assumption.
      + assumption.
    - eapply bs_While_True.
      + apply Renaming.eval_renaming_invariance. assumption.
      + apply IHHbs1.
      + apply IHHbs2.
    - apply bs_While_False.
      apply Renaming.eval_renaming_invariance. assumption.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r) as [r' Hinv].
    apply (renaming_invariant_bs _ r') in Hbs.
    rewrite re_rename in Hbs by assumption.
    destruct c as [[st i] o], c' as [[st' i'] o'].
    simpl in Hbs.
    rewrite Renaming.re_rename_state in Hbs by assumption.
    rewrite Renaming.re_rename_state in Hbs by assumption.
    assumption.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent, eval. intros i o. split; intros [st H].
    - apply (renaming_invariant_bs _ r) in H.
      simpl in H. exists (Renaming.rename_state r st). assumption.
    - destruct (Renaming.renaming_inv2 r) as [r' Hinv].
      rewrite <- (Renaming.re_rename_state r r' Hinv nil) in H.
      rewrite <- (Renaming.re_rename_state r r' Hinv st) in H.
      apply (renaming_invariant_bs_inv s r
               (Renaming.rename_state r' nil, i, nil)
               (Renaming.rename_state r' st, nil, o)) in H.
      simpl in H.
      exists (Renaming.rename_state r' st). assumption.
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
  induction EXEC; intros S DEF; subst.
  - discriminate.
  - cps_bs_gen_helper k DEF bs_Skip.
  - cps_bs_gen_helper k DEF bs_Assign.
  - cps_bs_gen_helper k DEF bs_Read.
  - cps_bs_gen_helper k DEF bs_Write.
  - destruct k; inversion DEF; subst.
    + apply IHEXEC. reflexivity.
    + apply SmokeTest.seq_assoc. apply IHEXEC. reflexivity.
  - destruct k; inversion DEF; subst.
    + apply bs_If_True.
      * assumption.
      * apply IHEXEC. reflexivity.
    + assert (HSeq : (s, i, o) == s1 ;; s0 ==> c').
      { apply IHEXEC. reflexivity. }
      inversion HSeq; subst.
      eapply bs_Seq.
      * apply bs_If_True; eauto.
      * eauto.
  - destruct k; inversion DEF; subst.
    + apply bs_If_False.
      * assumption.
      * apply IHEXEC. reflexivity.
    + assert (HSeq : (s, i, o) == s2 ;; s0 ==> c').
      { apply IHEXEC. reflexivity. }
      inversion HSeq; subst.
      eapply bs_Seq.
      * apply bs_If_False; eauto.
      * eauto.
  - destruct k; inversion DEF; subst.
    + assert (HSeq : (st, i, o) == s ;; WHILE e DO s END ==> c').
      { apply IHEXEC. reflexivity. }
      inversion HSeq; subst.
      eapply bs_While_True; eauto.
    + assert (HSeq : (st, i, o) == s ;; (WHILE e DO s END ;; s0) ==> c').
      { apply IHEXEC. reflexivity. }
      inversion HSeq; subst. inversion STEP2; subst.
      eapply bs_Seq.
      * eapply bs_While_True; eauto.
      * eauto.
  - destruct k; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_While_False. assumption.
    + eapply bs_Seq.
      * apply bs_While_False. assumption.
      * apply IHEXEC. reflexivity.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  eapply cps_bs_gen; eauto.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
  eapply cps_bs_gen; eauto.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  unfold Kapp in *.
  destruct k1.
  - destruct k2.
    + assumption.
    + destruct k3; inversion STEP.
  - destruct k2.
    + assumption.
    + destruct k3; constructor; unfold Kapp; assumption.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  generalize dependent k.
  induction EXEC; intros k STEP; inversion STEP; subst.
  - assumption.
  - eapply cps_Assign; eauto.
  - apply cps_Read. assumption.
  - eapply cps_Write; eauto.
  - apply cps_Seq. apply IHEXEC1.
    destruct k.
    + apply cps_Skip. apply IHEXEC2. assumption.
    + apply cps_Skip. apply cps_Seq. apply IHEXEC2. assumption.
  - apply cps_If_True.
    + assumption.
    + apply IHEXEC. assumption.
  - apply cps_If_False.
    + assumption.
    + apply IHEXEC. assumption.
  - apply cps_While_True.
    + assumption.
    + destruct k.
      * apply IHEXEC1. apply cps_Skip. apply IHEXEC2. assumption.
      * apply IHEXEC1. apply cps_Skip. apply cps_Seq. apply IHEXEC2. assumption.
  - apply cps_While_False; auto.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont.
  - apply EXEC.
  - apply cps_Skip. apply cps_Empty.
Qed.
