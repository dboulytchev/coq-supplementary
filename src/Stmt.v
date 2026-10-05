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
Proof. exact (H Hole). Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists SKIP, ((Id 0) ::= Nat 0). split.
  - intros inp out. split; intros [st RUN].
    + inversion RUN; subst. exists (update Z nil (Id 0) 0%Z).
      apply bs_Assign. constructor.
    + inversion RUN; subst. exists ([] : state Z). constructor.
  - intro SAME.
    specialize (SAME (SeqL Hole (WRITE (Var (Id 0)))) nil (0%Z :: nil)).
    destruct SAME as [_ BACK].
    assert (GOOD : eval (((Id 0) ::= Nat 0) ;; WRITE (Var (Id 0))) nil (0%Z :: nil)).
    { exists (update Z nil (Id 0) 0%Z).
      eapply bs_Seq with (c' := (update Z nil (Id 0) 0%Z, [], [])).
      - apply bs_Assign. constructor.
      - apply bs_Write. apply bs_Var. constructor. }
    apply BACK in GOOD. destruct GOOD as [st RUN].
    inversion RUN; subst. inversion STEP1; subst.
    inversion STEP2; subst. inversion VAL; subst. inversion VAR.
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
    intros c c'. split; intro EXEC.
    - inversion EXEC; subst. inversion STEP1; subst.
      eapply bs_Seq; [eassumption | eapply bs_Seq; eassumption].
    - inversion EXEC; subst. inversion STEP2; subst.
      eapply bs_Seq; [eapply bs_Seq; eassumption | eassumption].
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    intros c c'. split; intro RUN.
    - inversion RUN; subst.
      + eapply bs_If_True; eauto using bs_Seq.
      + eapply bs_If_False; eauto using bs_Skip.
    - inversion RUN; subst.
      + inversion STEP; subst. eapply bs_While_True; eauto.
      + inversion STEP; subst. apply bs_While_False; assumption.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as loop eqn:Hloop.
    remember (st, i, o) as final eqn:Hfinal.
    induction EXE; inversion Hloop; subst.
    - apply IHEXE2; reflexivity.
    - inversion Hfinal; subst. exact CVAL.
  Qed.

  (* A terminating derivation cannot have a permanently true guard. *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro RUN. remember (WHILE (Nat 1) DO s END) as loop eqn:Hloop.
    induction RUN; inversion Hloop; subst.
    - apply IHRUN2; reflexivity.
    - inversion CVAL.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    intros c c'. split; intro RUN.
    - exfalso. eapply while_true_undefined; exact RUN.
    - inversion RUN; subst; inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    intros c c'. split; intro RUN.
    - remember (WHILE e DO s1 END) as loop eqn:Hloop.
      induction RUN; inversion Hloop; subst.
      + eapply bs_While_True.
        * exact CVAL.
        * apply (proj1 (EQ _ _)); exact RUN1.
        * apply IHRUN2; reflexivity.
      + eapply bs_While_False; exact CVAL.
    - remember (WHILE e DO s2 END) as loop eqn:Hloop.
      induction RUN; inversion Hloop; subst.
      + eapply bs_While_True.
        * exact CVAL.
        * apply (proj2 (EQ _ _)); exact RUN1.
        * apply IHRUN2; reflexivity.
      + eapply bs_While_False; exact CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  intros c c'. split; intro EXEC; inversion EXEC; subst;
    eapply bs_Seq; eauto; now apply EQ.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  intros c c'. split; intro EXEC; inversion EXEC; subst;
    eapply bs_Seq; eauto; now apply EQ.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  intros c c'. split; intro EXEC; inversion EXEC; subst;
    eauto using bs_If_True, bs_If_False;
    eapply bs_If_False; eauto; now apply EQ.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  intros c c'. split; intro EXEC; inversion EXEC; subst;
    eauto using bs_If_True, bs_If_False;
    eapply bs_If_True; eauto; now apply EQ.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. now apply SmokeTest.while_eq. Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  repeat match goal with |- _ /\ _ => split end.
  - now apply eq_congruence_seq_r.
  - now apply eq_congruence_seq_l.
  - now apply eq_congruence_cond_else.
  - now apply eq_congruence_cond_then.
  - now apply eq_congruence_while.
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
  all: try (assert (z = z0) by (eapply eval_deterministic; eauto);
            subst; reflexivity).
  all: try solve [eval_zero_not_one | eauto].
  - pose proof (IHEXEC1_1 _ STEP1) as SAME.
    subst c'0. eauto.
  - pose proof (IHEXEC1_1 _ STEP) as SAME.
    subst c'0. eauto.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma equivalent_states_update (s1 s2 : state Z) (x : id) (z : Z)
      (EQ : equivalent_states s1 s2) :
  equivalent_states (s1 [x <- z]) (s2 [x <- z]).
Proof.
  intros y n. unfold Expr.equivalent_states.
  destruct (id_eq_dec x y) as [SAME | OTHER].
  - subst y. split; intro BIND;
      assert (n = z) by (eapply state_deterministic; [exact BIND | apply update_eq]);
      subst n; apply update_eq.
  - assert (DISTINCT : x <> y) by exact OTHER.
    split; intro BIND.
    + apply (proj1 (update_neq Z s2 x y z n DISTINCT)).
      apply (proj1 (EQ y n)).
      now apply (proj2 (update_neq Z s1 x y z n DISTINCT)).
    + apply (proj1 (update_neq Z s1 x y z n DISTINCT)).
      apply (proj2 (EQ y n)).
      now apply (proj2 (update_neq Z s2 x y z n DISTINCT)).
Qed.

(* Keep the configurations general during induction; only afterwards
   identify their state, input and output components. *)
Lemma bs_equiv_states_aux s c c' (RUN : bs_int s c c') :
  forall st inp out fin inp' out' alt,
    c = (st, inp, out) -> c' = (fin, inp', out') ->
    equivalent_states st alt ->
    exists alt', equivalent_states fin alt' /\
                 bs_int s (alt, inp, out) (alt', inp', out').
Proof.
  induction RUN; intros initial input output final input' output' alt SOURCE DEST EQ;
    inversion SOURCE; subst; try (inversion DEST; subst).
  - exists alt. split; [exact EQ | constructor].
  - exists (alt [x <- z]). split.
    + apply equivalent_states_update. exact EQ.
    + apply bs_Assign. eapply variable_relevance; eauto.
  - exists (alt [x <- z]). split.
    + apply equivalent_states_update. exact EQ.
    + constructor.
  - exists alt. split.
    + exact EQ.
    + apply bs_Write. eapply variable_relevance; eauto.
  - destruct c' as [[mid inp] out].
    destruct (IHRUN1 initial input output mid inp out alt (Logic.eq_refl _) (Logic.eq_refl _) EQ)
      as [mid' [MID STEP1']].
    destruct (IHRUN2 mid inp out final input' output' mid' (Logic.eq_refl _) (Logic.eq_refl _) MID)
      as [fin' [FIN STEP2']].
    exists fin'. split; [exact FIN | eapply bs_Seq; eauto].
  - destruct (IHRUN initial input output final input' output' alt (Logic.eq_refl _) (Logic.eq_refl _) EQ)
      as [fin' [FIN STEP']].
    exists fin'. split.
    + exact FIN.
    + eapply bs_If_True; [eapply variable_relevance; eauto | exact STEP'].
  - destruct (IHRUN initial input output final input' output' alt (Logic.eq_refl _) (Logic.eq_refl _) EQ)
      as [fin' [FIN STEP']].
    exists fin'. split.
    + exact FIN.
    + eapply bs_If_False; [eapply variable_relevance; eauto | exact STEP'].
  - destruct c' as [[mid inp] out].
    destruct (IHRUN1 initial input output mid inp out alt (Logic.eq_refl _) (Logic.eq_refl _) EQ)
      as [mid' [MID STEP1']].
    destruct (IHRUN2 mid inp out final input' output' mid' (Logic.eq_refl _) (Logic.eq_refl _) MID)
      as [fin' [FIN STEP2']].
    exists fin'. split.
    + exact FIN.
    + eapply bs_While_True;
        [eapply variable_relevance; eauto | exact STEP1' | exact STEP2'].
  - exists alt. split.
    + exact EQ.
    + apply bs_While_False. eapply variable_relevance; eauto.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2', equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  eapply bs_equiv_states_aux; [exact H | reflexivity | reflexivity | exact HE1].
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
    revert c'' EXEC2. induction EXEC1; intros target EXEC2;
      inversion EXEC2; subst; try reflexivity;
      try (assert (z = z0) by (eapply eval_deterministic; eauto);
           subst; reflexivity);
      try (eval_zero_not_one);
      try (pose proof (IHEXEC1 _ SSTEP) as SAME; congruence).
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    revert c'' STEP2. induction STEP1; intros dest SECOND; inversion SECOND; subst;
      match goal with
      | H1 : ss_int_step ?p ?cfg ?r1, H2 : ss_int_step ?p ?cfg ?r2 |- _ =>
          pose proof (ss_int_step_deterministic p cfg r1 r2 H1 H2) as SAME
      end;
      inversion SAME; subst; eauto.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. inversion STEP; subst; eauto using bs_int. Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    induction STEP1.
    - eapply ss_int_Step.
      + apply ss_Seq_Compl. exact H.
      + exact STEP2.
    - eapply ss_int_Step.
      + apply ss_Seq_InCompl. exact H.
      + apply IHSTEP1. exact STEP2.
  Qed.
  
  Lemma ss_bs_step_aux s c result (STEP : ss_int_step s c result) :
    forall t next finish, result = (Some t, next) ->
      bs_int t next finish -> bs_int s c finish.
  Proof.
    induction STEP; intros t next finish SAME RUN; inversion SAME; subst.
    - eapply bs_Seq.
      + apply ss_bs_base. exact STEP.
      + exact RUN.
    - inversion RUN; subst.
      eapply bs_Seq.
      + eapply IHSTEP; [reflexivity | eassumption].
      + eassumption.
    - eapply bs_If_True; eauto.
    - eapply bs_If_False; eauto.
    - apply (proj2 (SmokeTest.while_unfolds e s _ _)). exact RUN.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof. eapply ss_bs_step_aux; [exact STEP | reflexivity | exact EXEC]. Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intro RUN.
    - induction RUN.
      + apply ss_int_Base, ss_Skip.
      + apply ss_int_Base, ss_Assign. exact VAL.
      + apply ss_int_Base, ss_Read.
      + apply ss_int_Base, ss_Write. exact VAL.
      + eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step.
        * apply ss_If_True. exact CVAL.
        * exact IHRUN.
      + eapply ss_int_Step.
        * apply ss_If_False. exact CVAL.
        * exact IHRUN.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_True. exact CVAL.
          -- eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_False. exact CVAL.
          -- apply ss_int_Base, ss_Skip.
    - induction RUN.
      + apply ss_bs_base. exact H.
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
    induction s; simpl; try reflexivity;
      try (rewrite Renaming.re_rename_expr by exact Hinv);
      try (rewrite Hinv);
      try (rewrite IHs1, IHs2);
      try (rewrite IHs); reflexivity.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. destruct r as [f Hf]. reflexivity. Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r as [f BI]. induction Hbs; simpl.
    - constructor.
    - apply bs_Assign.
      apply (proj1 (Renaming.eval_renaming_invariance _ _ _ (exist _ f BI))). exact VAL.
    - constructor.
    - apply bs_Write.
      apply (proj1 (Renaming.eval_renaming_invariance _ _ _ (exist _ f BI))). exact VAL.
    - eapply bs_Seq; eauto.
    - eapply bs_If_True; eauto.
      apply (proj1 (Renaming.eval_renaming_invariance _ _ _ (exist _ f BI))). exact CVAL.
    - eapply bs_If_False; eauto.
      apply (proj1 (Renaming.eval_renaming_invariance _ _ _ (exist _ f BI))). exact CVAL.
    - eapply bs_While_True; eauto.
      apply (proj1 (Renaming.eval_renaming_invariance _ _ _ (exist _ f BI))). exact CVAL.
    - eapply bs_While_False.
      apply (proj1 (Renaming.eval_renaming_invariance _ _ _ (exist _ f BI))). exact CVAL.
  Qed.

  Lemma rename_conf_inv r r' (INV : Renaming.renamings_inv r' r) c :
    rename_conf r' (rename_conf r c) = c.
  Proof.
    destruct c as [[st inp] out]. simpl.
    now rewrite (Renaming.re_rename_state r' r INV).
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r) as [r' INV].
    replace c with (rename_conf r' (rename_conf r c)) by
      (apply rename_conf_inv; exact INV).
    replace c' with (rename_conf r' (rename_conf r c')) by
      (apply rename_conf_inv; exact INV).
    replace s with (rename r' (rename r s)) by
      (apply re_rename; exact INV).
    now apply renaming_invariant_bs.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    intros inp out. split; intros [st EXEC].
    - exists (Renaming.rename_state r st).
      change (bs_int (rename r s) (rename_conf r ([], inp, []))
                     (rename_conf r (st, [], out))).
      now apply renaming_invariant_bs.
    - destruct (Renaming.renaming_inv2 r) as [r' INV].
      exists (Renaming.rename_state r' st).
      apply renaming_invariant_bs_inv with (r := r).
      change (bs_int (rename r s) (rename_conf r ([], inp, []))
                     (rename_conf r (Renaming.rename_state r' st, [], out))).
      simpl. rewrite (Renaming.re_rename_state r r' INV). exact EXEC.
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
  revert S DEF. induction EXEC; intros target DEF; simpl in DEF.
  - discriminate DEF.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst. constructor.
    + eapply bs_Seq with (c' := c).
      * constructor.
       * apply IHEXEC with (S := s). reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Assign. exact CVAL.
    + eapply bs_Seq with (c' := (s [x <- n], i, o)).
      * apply bs_Assign. exact CVAL.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Read.
    + eapply bs_Seq with (c' := (s [x <- z], i, o)).
      * apply bs_Read.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Write. exact CVAL.
    + eapply bs_Seq with (c' := (s, i, z :: o)).
      * apply bs_Write. exact CVAL.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + eapply IHEXEC. reflexivity.
    + apply (proj2 (SmokeTest.seq_assoc s1 s2 s c c')).
      eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + eapply bs_If_True; [exact CVAL | apply IHEXEC with (S := s1); reflexivity].
    + assert (RUN : (s, i, o) == s1 ;; s0 ==> c')
        by (apply IHEXEC; reflexivity).
      inversion RUN; subst.
      eapply bs_Seq; [eapply bs_If_True; eauto | eassumption].
  - destruct k; simpl in DEF; inversion DEF; subst.
    + eapply bs_If_False; [exact CVAL | apply IHEXEC with (S := s2); reflexivity].
    + assert (RUN : (s, i, o) == s2 ;; s0 ==> c')
        by (apply IHEXEC; reflexivity).
      inversion RUN; subst.
      eapply bs_Seq; [eapply bs_If_False; eauto | eassumption].
  - destruct k; simpl in DEF; inversion DEF; subst.
    + assert (RUN : (st, i, o) == s ;; WHILE e DO s END ==> c')
        by (apply IHEXEC; reflexivity).
      inversion RUN; subst.
      eapply bs_While_True; eauto.
    + assert (RUN : (st, i, o) == s ;; (WHILE e DO s END ;; s0) ==> c')
        by (apply IHEXEC; reflexivity).
      inversion RUN; subst. inversion STEP2; subst.
      eapply bs_Seq.
      * eapply bs_While_True; eauto.
      * eassumption.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_While_False. exact CVAL.
    + eapply bs_Seq with (c' := (st, i, o)).
      * apply bs_While_False. exact CVAL.
      * eapply IHEXEC. reflexivity.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. eapply cps_bs_gen; [exact STEP | reflexivity]. Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. eapply cps_bs_gen; [exact STEP | reflexivity]. Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1.
  - destruct k2, k3; simpl in *;
      [exact STEP | inversion STEP | inversion STEP | inversion STEP].
  - destruct k2; simpl in *.
    + exact STEP.
    + apply cps_Seq. exact STEP.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  revert c3 k STEP. induction EXEC; intros fin k CONT.
  - exact CONT.
  - inversion CONT; subst. eapply cps_Assign; eauto.
  - inversion CONT; subst. eapply cps_Read; eauto.
  - inversion CONT; subst. eapply cps_Write; eauto.
  - apply cps_Seq. apply IHEXEC1.
    apply cps_Skip. destruct k; simpl.
    + apply IHEXEC2. exact CONT.
    + apply cps_Seq. apply IHEXEC2. exact CONT.
  - apply cps_If_True; [exact CVAL | apply IHEXEC; exact CONT].
  - apply cps_If_False; [exact CVAL | apply IHEXEC; exact CONT].
  - apply cps_While_True.
    + exact CVAL.
    + apply IHEXEC1. apply cps_Skip. destruct k; simpl.
      * apply IHEXEC2. exact CONT.
      * apply cps_Seq. apply IHEXEC2. exact CONT.
  - inversion CONT; subst. eapply cps_While_False; eauto.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont;
    [exact EXEC | apply cps_Skip, cps_Empty].
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
