Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

From hahn Require Import HahnBase.
From Stdlib Require Import Program.Equality.

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
  specialize (H Hole). simpl in H. assumption.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists SKIP, (Id 1 ::= Nat 1).
  split.
  - (* ~e~: оба завершаются, оставляя выход пустым *)
    intros i o; split; intros [st H]; inversion H; subst.
    + exists [(Id 1, 1%Z)]. apply bs_Assign, bs_Nat.
    + exists []. apply bs_Skip.
  - (* ~c~: различаются контекстом [_ ;; WRITE (Var (Id 1))] *)
    intros HC.
    specialize (HC (SeqL Hole (WRITE (Var (Id 1)))) nil (1%Z :: nil)).
    destruct HC as [_ H]. simpl in H.
    destruct H as [st H].
    + exists [(Id 1, 1%Z)].
      eapply bs_Seq.
      * apply bs_Assign, bs_Nat.
      * apply bs_Write, bs_Var, st_binds_hd.
    + (* SKIP не может выдать [1] в выход *)
      inversion H; subst.
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
    split; intros H; seq_inversion; seq_inversion; seq_apply.
  Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    split; intros H.
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
    remember (st, i, o) as final.
    induction EXE; try discriminate.
    - apply IHEXE2; assumption.
    - injection Heqloop; injection Heqfinal; intros; subst.
      assumption.
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    split; intros H; inversion H; subst; inversion CVAL.
    destruct c' as [[sta inp] outp].
    apply while_false in H. inversion H.
  Qed.

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    split; intros H; dependent induction H; eauto.
    - eapply bs_While_True; eauto. apply EQ. assumption.
    - eapply bs_While_True; eauto. apply EQ. assumption.
  Qed.

  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro H.
    remember (WHILE (Nat 1) DO s END) as loop.
    induction H; inversion Heqloop; subst; auto.
    inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  split; intros H; seq_inversion; eapply bs_Seq; eauto; apply EQ; assumption.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  split; intros H; seq_inversion; eapply bs_Seq; eauto; apply EQ; assumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  split; intros H; inversion H; subst.
  - apply bs_If_True; assumption.
  - apply bs_If_False; auto. apply EQ. assumption.
  - apply bs_If_True; assumption.
  - apply bs_If_False; auto. apply EQ. assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  split; intros H; inversion H; subst.
  - apply bs_If_True; auto. apply EQ. assumption.
  - apply bs_If_False; assumption.
  - apply bs_If_True; auto. apply EQ. assumption.
  - apply bs_If_False; assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  apply SmokeTest.while_eq; assumption.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. apply eq_congruence_seq_r; assumption.
  split. apply eq_congruence_seq_l; assumption.
  split. apply eq_congruence_cond_else; assumption.
  split. apply eq_congruence_cond_then; assumption.
  apply eq_congruence_while; assumption.
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
  induction EXEC1; intros c2 EXEC2; inversion EXEC2; subst; auto;
  try by_eval_deterministic;
  try eval_zero_not_one;
  try (apply IHEXEC1_2; apply IHEXEC1_1 in STEP1; subst; assumption);
  try (apply IHEXEC1; assumption);
  try (apply IHEXEC1_2; apply IHEXEC1_1 in STEP; subst; assumption).
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

(* Эквивалентность состояний сохраняется при синхронном обновлении. *)
Lemma equivalent_states_update (st st' : state Z) (x : id) (z : Z)
      (HE : equivalent_states st st') :
  equivalent_states (st [x <- z]) (st' [x <- z]).
Proof.
  intros y v. split; intro H; inversion H; subst.
  - apply st_binds_hd.
  - apply st_binds_tl; auto. apply HE. assumption.
  - apply st_binds_hd.
  - apply st_binds_tl; auto. apply HE. assumption.
Qed.

(* Если состояния эквивалентны, выражение вычисляется в них одинаково. *)
Lemma eval_equiv_states (e : expr) (st st' : state Z) (z : Z)
      (HE : equivalent_states st st')
      (EV : [| e |] st => z) :
  [| e |] st' => z.
Proof.
  apply (variable_relevance e st st' z); auto.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')  
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  revert st1' HE1.
  dependent induction H; intros stp HE.
  - (* Skip *)
    exists stp. split; auto.
  - (* Assign *)
    exists (stp [x <- z]). split.
    + apply equivalent_states_update; auto.
    + apply bs_Assign. eapply eval_equiv_states; eauto.
  - (* Read *)
    exists (stp [x <- z]). split.
    + apply equivalent_states_update; auto.
    + apply bs_Read.
  - (* Write *)
    exists stp. split; auto.
    apply bs_Write. eapply eval_equiv_states; eauto.
  - (* Seq *)
    destruct c' as [[stm im] om].
    edestruct IHbs_int1 as [stm' [HEm Hm]]; try reflexivity; try eassumption.
    edestruct IHbs_int2 as [st2' [HE2 H2]]; try reflexivity; try eassumption.
    exists st2'. split; auto. eapply bs_Seq; eauto.
  - (* If_True *)
    edestruct IHbs_int as [st2' [HE2 H2]]; eauto.
    exists st2'. split; auto.
    apply bs_If_True; auto. eapply eval_equiv_states; eauto.
  - (* If_False *)
    edestruct IHbs_int as [st2' [HE2 H2]]; eauto.
    exists st2'. split; auto.
    apply bs_If_False; auto. eapply eval_equiv_states; eauto.
  - (* While_True *)
    destruct c' as [[stm im] om].
    edestruct IHbs_int1 as [stm' [HEm Hm]]; eauto.
    edestruct IHbs_int2 as [st2' [HE2 H2]]; eauto.
    exists st2'. split; auto.
    eapply bs_While_True; eauto. eapply eval_equiv_states; eauto.
  - (* While_False *)
    exists stp. split; auto.
    apply bs_While_False. eapply eval_equiv_states; eauto.
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
    induction EXEC1; intros c'' EXEC2; inversion EXEC2; subst; auto;
    try by_eval_deterministic;
    try eval_zero_not_one;
    try (apply IHEXEC1 in SSTEP; injection SSTEP;
         intros; try discriminate; subst; auto).
  Qed.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''.
    induction STEP1; intros cx STEP2; inversion STEP2; subst.
    - pose proof (ss_int_step_deterministic _ _ _ _ H H0) as Heq.
      injection Heq. intros. subst. reflexivity.
    - exfalso. pose proof (ss_int_step_deterministic _ _ _ _ H H0) as Heq. discriminate.
    - exfalso. pose proof (ss_int_step_deterministic _ _ _ _ H H0) as Heq. discriminate.
    - apply IHSTEP1.
      pose proof (ss_int_step_deterministic _ _ _ _ H H0) as Heq.
      injection Heq. intros. subst. assumption.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP; subst; econstructor; eauto.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'.
  Proof.
    generalize dependent c'.
    induction STEP1; intros c2 STEP2.
    - eapply ss_int_Step.
      + apply ss_Seq_Compl. eassumption.
      + assumption.
    - eapply ss_int_Step.
      + apply ss_Seq_InCompl. eassumption.
      + apply IHSTEP1. assumption.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent c''.
    dependent induction s; intros c'' EXEC; inversion STEP; subst; eauto.
    - eapply bs_Seq.
      + apply ss_bs_base. eassumption.
      + assumption.
    - inversion EXEC; subst. eapply bs_Seq; eauto.
    - inversion EXEC; subst.
      + inversion STEP0; subst. eapply bs_While_True; eauto.
      + inversion STEP0; subst. apply bs_While_False. assumption.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intro H.
    - induction H.
      + apply ss_int_Base. apply ss_Skip.
      + apply ss_int_Base. apply ss_Assign. assumption.
      + apply ss_int_Base. apply ss_Read.
      + apply ss_int_Base. apply ss_Write. assumption.
      + eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step.
        * apply ss_If_True. eassumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_If_False. eassumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          { apply ss_If_True. eassumption. }
          eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          { apply ss_If_False. eassumption. }
          apply ss_int_Base. apply ss_Skip.
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
    induction s; simpl.
    - reflexivity.
    - rewrite Renaming.re_rename_expr by assumption.
      rewrite Hinv. reflexivity.
    - rewrite Hinv. reflexivity.
    - rewrite Renaming.re_rename_expr by assumption. reflexivity.
    - rewrite IHs1, IHs2. reflexivity.
    - rewrite Renaming.re_rename_expr by assumption.
      rewrite IHs1, IHs2. reflexivity.
    - rewrite Renaming.re_rename_expr by assumption.
      rewrite IHs. reflexivity.
  Qed.

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    destruct r as [f Hbij]. unfold update. simpl. reflexivity.
  Qed.

  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r as [f Hb] eqn:Hreq.
    induction Hbs; simpl.
    - apply bs_Skip.
    - apply bs_Assign. apply Renaming.eval_renaming_invariance. assumption.
    - apply bs_Read.
    - apply bs_Write. apply Renaming.eval_renaming_invariance. assumption.
    - eapply bs_Seq; eauto.
    - apply bs_If_True; auto. apply Renaming.eval_renaming_invariance. assumption.
    - apply bs_If_False; auto. apply Renaming.eval_renaming_invariance. assumption.
    - eapply bs_While_True; eauto. apply Renaming.eval_renaming_invariance. assumption.
    - apply bs_While_False. apply Renaming.eval_renaming_invariance. assumption.
  Qed.

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r) as [r' Hinv].
    apply (renaming_invariant_bs _ r') in Hbs.
    rewrite (re_rename r' r Hinv) in Hbs.
    destruct c as [[st1 i1] o1]. destruct c' as [[st2 i2] o2].
    simpl in Hbs.
    rewrite (Renaming.re_rename_state r' r Hinv st1) in Hbs.
    rewrite (Renaming.re_rename_state r' r Hinv st2) in Hbs.
    assumption.
  Qed.

  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    split; intros [st H].
    - exists (Renaming.rename_state r st).
      apply (renaming_invariant_bs s r) in H. simpl in H. assumption.
    - destruct (Renaming.renaming_inv r) as [r' Hinv].
      exists (Renaming.rename_state r' st).
      apply (renaming_invariant_bs (rename r s) r') in H.
      rewrite (re_rename r' r Hinv) in H. simpl in H. assumption.
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
  induction EXEC; intros S DEF; try discriminate.
  - (* Skip *)
    destruct k eqn:K; subst; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Skip.
    + eapply bs_Seq. apply bs_Skip. apply IHEXEC. simpl. reflexivity.
  - (* Assign *)
    destruct k eqn:K; subst; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Assign. assumption.
    + eapply bs_Seq. apply bs_Assign. eassumption. apply IHEXEC. simpl. reflexivity.
  - (* Read *)
    destruct k eqn:K; subst; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Read.
    + eapply bs_Seq. apply bs_Read. apply IHEXEC. simpl. reflexivity.
  - (* Write *)
    destruct k eqn:K; subst; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Write. assumption.
    + eapply bs_Seq. apply bs_Write. eassumption. apply IHEXEC. simpl. reflexivity.
  - (* Seq *)
    destruct k eqn:K; subst; inversion DEF; subst.
    + apply IHEXEC. simpl. reflexivity.
    + assert (Hh : c == s1 ;; s2 ;; s ==> c').
      { apply IHEXEC. simpl. reflexivity. }
      seq_inversion. seq_inversion. eapply bs_Seq.
      2: { eassumption. }
      eapply bs_Seq; eassumption.
  - (* If_True *)
    destruct k eqn:K; subst; inversion DEF; subst.
    + apply bs_If_True. assumption.
      apply IHEXEC. simpl. reflexivity.
    + assert (Hh : (s, i, o) == s1 ;; s0 ==> c').
      { apply IHEXEC. simpl. reflexivity. }
      seq_inversion. eapply bs_Seq.
      2: { eassumption. }
      apply bs_If_True; assumption.
  - (* If_False *)
    destruct k eqn:K; subst; inversion DEF; subst.
    + apply bs_If_False. assumption.
      apply IHEXEC. simpl. reflexivity.
    + assert (Hh : (s, i, o) == s2 ;; s0 ==> c').
      { apply IHEXEC. simpl. reflexivity. }
      seq_inversion. eapply bs_Seq.
      2: { eassumption. }
      apply bs_If_False; assumption.
  - (* While_True *)
    destruct k eqn:K; subst; inversion DEF; subst.
    + assert (Hh : (st, i, o) == s ;; WHILE e DO s END ==> c').
      { apply IHEXEC. simpl. reflexivity. }
      seq_inversion. eapply bs_While_True; eauto.
    + assert (Hh : (st, i, o) == s ;; (WHILE e DO s END ;; s0) ==> c').
      { apply IHEXEC. simpl. reflexivity. }
      seq_inversion. seq_inversion. eapply bs_Seq.
      * eapply bs_While_True; eauto.
      * assumption.
  - (* While_False *)
    destruct k eqn:K; subst; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_While_False. assumption.
    + eapply bs_Seq.
      * apply bs_While_False. assumption.
      * apply IHEXEC. simpl. reflexivity.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. eapply cps_bs_gen; eauto. Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. eapply cps_bs_gen; eauto. Qed.

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
