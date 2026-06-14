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
  assumption.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists (Id 0 ::= Nat 0), (Id 0 ::= Nat 1).
  split.
  - unfold eval_equivalent, eval.
    intros i o; split; intros [st H]; inversion H; subst; inversion VAL; subst.
    + exists ((Id 0, Z.one) :: nil). constructor. constructor.
    + exists ((Id 0, Z.zero) :: nil). constructor. constructor.
  - unfold contextual_equivalent, eval_equivalent, eval.
    intros H.
    specialize (H (SeqL Hole (WRITE (Var (Id 0)))) nil (Z.zero :: nil)).
    simpl in H.
    destruct H as [H _].
    assert (exists st : state Z,
               (nil, nil, nil) == (Id 0 ::= Nat 0) ;; WRITE (Var (Id 0)) ==> (st, nil, Z.zero :: nil)) as HEX.
    { eexists.
      eapply bs_Seq.
      - apply bs_Assign. constructor.
      - apply bs_Write. constructor. constructor. }
    specialize (H HEX).
    destruct H as [st H].
    inversion H; subst.
    inversion STEP1; subst.
    inversion STEP2; subst.
    repeat match goal with
          | H : [| Nat _ |] _ => _ |- _ => inversion H; subst; clear H
          | H : [| Var _ |] _ => _ |- _ => inversion H; subst; clear H
          | H : _ / _ => _ |- _ => inversion H; subst; clear H
          end;
      congruence.
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
    intros c c'; split; intros H; repeat seq_inversion; seq_apply.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros c c'; split; intros H.
    - inversion H; subst.
      + eapply bs_If_True.
        * eassumption.
        *
        eapply bs_Seq; eauto.
      + eapply bs_If_False.
        * eassumption.
        *
        constructor.
    - inversion H; subst.
      + inversion STEP; subst.
        eapply bs_While_True; eauto.
      + inversion STEP; subst.
        constructor; assumption.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as w eqn:HW.
    remember (st, i, o) as cf eqn:HCF.
    induction EXE; inversion HW; subst;
      repeat match goal with
            | H : (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
            | H : (?a, ?b, ?c) = (?x, ?y, ?z) |- _ => inversion H; subst; clear H
            | H : ?c = (_, _, _) |- _ => inversion H; subst; clear H
            | H : (_, _, _) = ?c |- _ => inversion H; subst; clear H
            end.
    - apply IHEXE2; reflexivity.
    - assumption.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros c c'; split; intros H.
    - exfalso.
      remember (WHILE (Nat 1) DO SKIP END) as w eqn:HW.
      induction H; inversion HW; subst.
      + eauto.
      + inversion CVAL.
    - inversion H; subst; inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent in *.
    intros c c'; split; intros H.
    - remember (WHILE e DO s1 END) as w eqn:HW.
      induction H; inversion HW; subst.
      + eapply bs_While_True; eauto.
        apply EQ; eauto.
      + constructor; assumption.
    - remember (WHILE e DO s2 END) as w eqn:HW.
      induction H; inversion HW; subst.
      + eapply bs_While_True; eauto.
        apply EQ; eauto.
      + constructor; assumption.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intros H.
    remember (WHILE (Nat 1) DO s END) as w eqn:HW.
    induction H; inversion HW; subst.
    - eauto.
    - inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent in *.
  intros c c'; split; intros H; inversion H; subst;
    eapply bs_Seq; eauto; apply EQ; assumption.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent in *.
  intros c c'; split; intros H; inversion H; subst;
    eapply bs_Seq; eauto; apply EQ; assumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent in *.
  intros c c'; split; intros H; inversion H; subst;
    [eapply bs_If_True | eapply bs_If_False | eapply bs_If_True | eapply bs_If_False];
    eauto; apply EQ; assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent in *.
  intros c c'; split; intros H; inversion H; subst;
    [eapply bs_If_True | eapply bs_If_False | eapply bs_If_True | eapply bs_If_False];
    eauto; apply EQ; assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  apply SmokeTest.while_eq.
  assumption.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split.
  { apply eq_congruence_seq_r; assumption. }
  split.
  { apply eq_congruence_seq_l; assumption. }
  split.
  { apply eq_congruence_cond_else; assumption. }
  split.
  { apply eq_congruence_cond_then; assumption. }
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
  revert c2 EXEC2.
  induction EXEC1; intros c2 EXEC2; inversion EXEC2; subst; try reflexivity.
  - assert (z = z0) by (eapply eval_deterministic; eauto).
    subst; reflexivity.
  - assert (z = z0) by (eapply eval_deterministic; eauto).
    subst; reflexivity.
  - assert (c' = c'0) by (eapply IHEXEC1_1; eauto).
    subst; eauto.
  - eauto.
  - eval_zero_not_one.
  - eval_zero_not_one.
  - eauto.
  - assert (c' = c'0) by (eapply IHEXEC1_1; eauto).
    subst; eauto.
  - eval_zero_not_one.
  - eval_zero_not_one.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma equivalent_states_update (st st' : state Z) (x : id) (z : Z)
      (HE : equivalent_states st st') :
  equivalent_states (st [x <- z]) (st' [x <- z]).
Proof.
  unfold equivalent_states, Expr.equivalent_states in *.
  intros y v; split; intros HB; destruct (id_eq_dec y x) as [EQ | NEQ].
  - subst.
    assert (v = z).
    { eapply state_deterministic; [exact HB | apply update_eq]. }
    subst; apply update_eq.
  - apply (proj1 (update_neq Z st' x y z v ltac:(congruence))).
    apply HE.
    apply (proj2 (update_neq Z st x y z v ltac:(congruence))).
    exact HB.
  - subst.
    assert (v = z).
    { eapply state_deterministic; [exact HB | apply update_eq]. }
    subst; apply update_eq.
  - apply (proj1 (update_neq Z st x y z v ltac:(congruence))).
    apply HE.
    apply (proj2 (update_neq Z st' x y z v ltac:(congruence))).
    exact HB.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')  
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  remember (st1, i, o) as c eqn:HC.
  remember (st2, i', o') as c' eqn:HC'.
  revert st1 st2 st1' i o i' o' HE1 HC HC'.
  induction H; intros st1 st2 st1' i0 o0 i'0 o'0 HE1 HC HC';
    inversion HC; inversion HC'; subst;
    repeat match goal with
          | H : (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
          | H : ?c = (_, _, _) |- _ => inversion H; subst; clear H
          | H : (_, _, _) = ?c |- _ => inversion H; subst; clear H
          end.
  - exists st1'. split; [assumption | constructor].
  - assert ([| e |] st1' => z) as VAL'.
    { eapply variable_relevance; eauto. }
    exists (st1' [x <- z]).
    split.
    { apply equivalent_states_update. assumption. }
    constructor. assumption.
  - exists (st1' [x <- z]).
    split.
    { apply equivalent_states_update. assumption. }
    constructor.
  - assert ([| e |] st1' => z) as VAL'.
    { eapply variable_relevance; eauto. }
    exists st1'. split; [assumption | constructor; assumption].
  - destruct c' as [[stm im] om].
    specialize (IHbs_int1 st1 stm st1' i0 o0 im om HE1 Logic.eq_refl Logic.eq_refl)
      as [stm' [Hstm EXEC1']].
    specialize (IHbs_int2 stm st2 stm' im om i'0 o'0 Hstm Logic.eq_refl Logic.eq_refl)
      as [st2' [Hst2 EXEC2']].
    exists st2'. split; [assumption | eapply bs_Seq; eauto].
  - assert ([| e |] st1' => Z.one) as CVAL'.
    { eapply variable_relevance; eauto. }
    specialize (IHbs_int st1 st2 st1' i0 o0 i'0 o'0 HE1 Logic.eq_refl Logic.eq_refl)
      as [st2' [Hst2 EXEC']].
    exists st2'. split; [assumption | eapply bs_If_True; eauto].
  - assert ([| e |] st1' => Z.zero) as CVAL'.
    { eapply variable_relevance; eauto. }
    specialize (IHbs_int st1 st2 st1' i0 o0 i'0 o'0 HE1 Logic.eq_refl Logic.eq_refl)
      as [st2' [Hst2 EXEC']].
    exists st2'. split; [assumption | eapply bs_If_False; eauto].
  - assert ([| e |] st1' => Z.one) as CVAL'.
    { eapply variable_relevance; eauto. }
    destruct c' as [[stm im] om].
    specialize (IHbs_int1 st1 stm st1' i0 o0 im om HE1 Logic.eq_refl Logic.eq_refl)
      as [stm' [Hstm EXEC1']].
    specialize (IHbs_int2 stm st2 stm' im om i'0 o'0 Hstm Logic.eq_refl Logic.eq_refl)
      as [st2' [Hst2 EXEC2']].
    exists st2'. split; [assumption | eapply bs_While_True; eauto].
  - assert ([| e |] st1' => Z.zero) as CVAL'.
    { eapply variable_relevance; eauto. }
    exists st1'. split; [assumption | constructor; assumption].
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
      subst; reflexivity.
    - assert (z = z0) by (eapply eval_deterministic; eauto).
      subst; reflexivity.
    - assert ((None, c') = (None, c'0)) by (eapply IHEXEC1; eauto).
      inversion H; reflexivity.
    - assert ((None, c') = (Some s1', c'0)) by (eapply IHEXEC1; eauto).
      discriminate.
    - assert ((Some s1', c') = (None, c'0)) by (eapply IHEXEC1; eauto).
      discriminate.
    - assert ((Some s1', c') = (Some s1'0, c'0)) by (eapply IHEXEC1; eauto).
      inversion H; reflexivity.
    - eval_zero_not_one.
    - eval_zero_not_one.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    revert c'' STEP2.
    induction STEP1; intros c''0 STEP2; inversion STEP2; subst;
      match goal with
      | H1 : c -- s --> ?x, H2 : c -- s --> ?y |- _ =>
        pose proof (ss_int_step_deterministic s c x y H1 H2) as HD;
        inversion HD; subst; eauto
      end.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP; subst; constructor; assumption.
  Qed.

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
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    remember (Some s', c') as r eqn:HR.
    revert s' c' HR c'' EXEC.
    induction STEP; intros sx cx HR c'' EXEC; inversion HR; subst; clear HR.
    - eapply bs_Seq.
      + eapply ss_bs_base; eauto.
      + exact EXEC.
    - inversion EXEC; subst.
      eapply bs_Seq.
      + eapply IHSTEP; eauto using Logic.eq_refl.
      + eauto.
    - eapply bs_If_True; eauto.
    - eapply bs_If_False; eauto.
    - apply (proj2 (SmokeTest.while_unfolds e s _ c'')).
      exact EXEC.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split.
    - intros EXEC.
      induction EXEC.
      + apply ss_int_Base. constructor.
      + apply ss_int_Base. constructor; assumption.
      + apply ss_int_Base. constructor.
      + apply ss_int_Base. constructor; assumption.
      + eapply ss_ss_composition; eauto.
      + eapply ss_int_Step.
        * apply ss_If_True; assumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_If_False; assumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_True; assumption.
          -- eapply ss_ss_composition; eauto.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_False; assumption.
          -- apply ss_int_Base. constructor.
    - intros EXEC.
      induction EXEC.
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
    induction s; simpl; f_equal; eauto using Expr.Renaming.re_rename_expr.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    unfold update.
    destruct r as [f Hf].
    reflexivity.
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
    - apply bs_Assign.
      apply (proj1 (Expr.Renaming.eval_renaming_invariance e s z (exist _ f Hf))).
      assumption.
    - apply bs_Read.
    - apply bs_Write.
      apply (proj1 (Expr.Renaming.eval_renaming_invariance e s z (exist _ f Hf))).
      assumption.
    - destruct c' as [[st_mid i_mid] o_mid].
      eapply bs_Seq; eauto.
    - eapply bs_If_True; eauto.
      apply (proj1 (Expr.Renaming.eval_renaming_invariance e s Z.one (exist _ f Hf))).
      assumption.
    - eapply bs_If_False; eauto.
      apply (proj1 (Expr.Renaming.eval_renaming_invariance e s Z.zero (exist _ f Hf))).
      assumption.
    - destruct c' as [[st_mid i_mid] o_mid].
      eapply bs_While_True; eauto.
      apply (proj1 (Expr.Renaming.eval_renaming_invariance e st Z.one (exist _ f Hf))).
      assumption.
    - eapply bs_While_False.
      apply (proj1 (Expr.Renaming.eval_renaming_invariance e st Z.zero (exist _ f Hf))).
      assumption.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Expr.Renaming.renaming_inv r) as [r' Hinv].
    pose proof (renaming_invariant_bs (rename r s) r' (rename_conf r c) (rename_conf r c') Hbs) as HH.
    rewrite re_rename in HH by exact Hinv.
    destruct c as [[st i] o].
    destruct c' as [[st' i'] o'].
    simpl in HH.
    rewrite Expr.Renaming.re_rename_state in HH by exact Hinv.
    rewrite Expr.Renaming.re_rename_state in HH by exact Hinv.
    exact HH.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent, eval.
    intros i o; split; intros [st H].
    - exists (Expr.Renaming.rename_state r st).
      exact (renaming_invariant_bs s r ([], i, []) (st, [], o) H).
    - destruct (Expr.Renaming.renaming_inv r) as [r' Hinv].
      exists (Expr.Renaming.rename_state r' st).
      pose proof (renaming_invariant_bs (rename r s) r' ([], i, []) (st, [], o) H) as HH.
      simpl in HH.
      rewrite re_rename in HH by exact Hinv.
      exact HH.
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
  induction EXEC; intros T DEF; simpl in DEF; try discriminate.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst. constructor.
    + eapply bs_Seq.
      * constructor.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Assign; exact CVAL.
    + eapply bs_Seq.
      * apply bs_Assign; exact CVAL.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Read.
    + eapply bs_Seq.
      * apply bs_Read.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst. apply bs_Write; exact CVAL.
    + eapply bs_Seq.
      * apply bs_Write; exact CVAL.
      * eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + eapply IHEXEC. reflexivity.
    + apply (proj2 (SmokeTest.seq_assoc s1 s2 s c c')).
      eapply IHEXEC. reflexivity.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + eapply bs_If_True.
      * exact CVAL.
      *
      eapply IHEXEC. reflexivity.
    + assert ((s, i, o) == s1 ;; s0 ==> c') as Hseq by (eapply IHEXEC; reflexivity).
      inversion Hseq; subst.
      eapply bs_Seq.
      * eapply bs_If_True; eauto.
      * eauto.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + eapply bs_If_False.
      * exact CVAL.
      *
      eapply IHEXEC. reflexivity.
    + assert ((s, i, o) == s2 ;; s0 ==> c') as Hseq by (eapply IHEXEC; reflexivity).
      inversion Hseq; subst.
      eapply bs_Seq.
      * eapply bs_If_False; eauto.
      * eauto.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + assert ((st, i, o) == s ;; WHILE e DO s END ==> c') as Hseq
        by (eapply IHEXEC; reflexivity).
      inversion Hseq; subst.
      eapply bs_While_True; eauto.
    + assert ((st, i, o) == s ;; (WHILE e DO s END ;; s0) ==> c') as Hseq
        by (eapply IHEXEC; reflexivity).
      inversion Hseq; subst.
      inversion STEP2; subst.
      eapply bs_Seq.
      * eapply bs_While_True; eauto.
      * eauto.
  - destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst.
      eapply bs_While_False; eauto.
    + eapply bs_Seq.
      * eapply bs_While_False; eauto.
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
  remember (k2 @ k3) as kk eqn:Hkk.
  revert k2 k3 Hkk.
  induction STEP; intros k2 k3 Hkk; subst; destruct k2; simpl in *.
  - destruct k3; simpl in Hkk; inversion Hkk; subst; constructor.
  - destruct k3; simpl in Hkk; inversion Hkk.
  - apply cps_Skip. exact STEP.
  - apply cps_Seq. apply cps_Skip. exact STEP.
  - apply cps_Assign with n; [exact CVAL | exact STEP].
  - apply cps_Seq. apply cps_Assign with n; [exact CVAL | exact STEP].
  - apply cps_Read. exact STEP.
  - apply cps_Seq. apply cps_Read. exact STEP.
  - apply cps_Write with z; [exact CVAL | exact STEP].
  - apply cps_Seq. apply cps_Write with z; [exact CVAL | exact STEP].
  - apply cps_Seq. exact STEP.
  - apply cps_Seq. apply cps_Seq. exact STEP.
  - apply cps_If_True; [exact CVAL | exact STEP].
  - apply cps_Seq. apply cps_If_True; [exact CVAL | exact STEP].
  - apply cps_If_False; [exact CVAL | exact STEP].
  - apply cps_Seq. apply cps_If_False; [exact CVAL | exact STEP].
  - apply cps_While_True; [exact CVAL | exact STEP].
  - apply cps_Seq. apply cps_While_True; [exact CVAL | exact STEP].
  - apply cps_While_False; [exact CVAL | exact STEP].
  - apply cps_Seq. apply cps_While_False; [exact CVAL | exact STEP].
Qed.

Lemma cps_skip_to_cont c c' k
      (STEP : k |- c -- !SKIP --> c') :
  KEmpty |- c -- k --> c'.
Proof.
  inversion STEP; subst.
  exact CSTEP.
Qed.

Lemma cps_stmt_to_empty_cont c c' s k
      (STEP : k |- c -- !s --> c') :
  KEmpty |- c -- !s @ k --> c'.
Proof.
  destruct k; simpl.
  - exact STEP.
  - eapply cps_cont_to_seq.
    simpl.
    exact STEP.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  revert c3 k STEP.
  induction EXEC; intros c3 k STEP.
  - exact STEP.
  - eapply cps_Assign.
    + exact VAL.
    + eapply cps_skip_to_cont. exact STEP.
  - eapply cps_Read.
    eapply cps_skip_to_cont. exact STEP.
  - eapply cps_Write.
    + exact VAL.
    + eapply cps_skip_to_cont. exact STEP.
  - apply cps_Seq.
    apply IHEXEC1.
    apply cps_Skip.
    apply cps_stmt_to_empty_cont.
    apply IHEXEC2.
    exact STEP.
  - eapply cps_If_True.
    + exact CVAL.
    + apply IHEXEC. exact STEP.
  - eapply cps_If_False.
    + exact CVAL.
    + apply IHEXEC. exact STEP.
  - eapply cps_While_True.
    + exact CVAL.
    + apply IHEXEC1.
      apply cps_Skip.
      apply cps_stmt_to_empty_cont.
      apply IHEXEC2.
      exact STEP.
  - eapply cps_While_False.
    + exact CVAL.
    + eapply cps_skip_to_cont. exact STEP.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont.
  - exact EXEC.
  - apply cps_Skip.
    constructor.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
