Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

Require Import Coq.Program.Equality.

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
Proof. eapply (H Hole). Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
    exists ((Id 1) ::= Nat 1).
    exists ((Id 1) ::= Nat 2).
    constructor.
    * constructor; intro.
      - dependent destruction H. dependent destruction H. econstructor. constructor. constructor.
      - dependent destruction H. dependent destruction H. econstructor. constructor. econstructor.
    * intro. specialize (H (SeqL Hole (WRITE (Var (Id 1)))) nil ([1%Z])). dependent destruction H.
      absurd (<| SeqL Hole (WRITE (Var (Id 1))) <~ Id 1 ::= Nat 2 |> [] => ([1%Z])).
      - intro. dependent destruction H1. dependent destruction H1. dependent destruction H1_.
        dependent destruction H1_0. dependent destruction VAL0. dependent destruction VAR.
        + dependent destruction VAL.
        + apply H1. reflexivity.
      - apply H. econstructor. econstructor.
        + constructor. constructor.
        + constructor. constructor. constructor.
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
    intro. intro. constructor; intro.
    * dependent destruction H. dependent destruction H.
      apply (bs_Seq _ c').
        assumption.
        apply (bs_Seq _ c''0).
          assumption.
          assumption.
    * dependent destruction H. dependent destruction H0.
      apply (bs_Seq _ c').
        apply (bs_Seq _ c0).
        assumption.
        assumption.
      assumption.
  Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    intro. intro. constructor; intro.
    * dependent destruction H.
      - apply bs_If_True. assumption.
        apply (bs_Seq _ c'). assumption. assumption.
      - apply bs_If_False. assumption. constructor.
    * dependent destruction H; dependent destruction H.
      - apply (bs_While_True _ _ _ c'). assumption. assumption. assumption.
      - constructor. assumption.
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    dependent induction EXE.
    * apply (IHEXE2 _ s _ i o). reflexivity. reflexivity.
    * assumption.
  Qed.

  Lemma loop_false (c c' : conf) (s : stmt)
    (H : c == WHILE (Nat 1) DO s END ==> c') : False.
  Proof.
    dependent induction H.
    - apply (IHbs_int2 s). reflexivity.
    - inversion CVAL.
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    intro. intro. constructor; intro.
    * exfalso. apply (loop_false _ _ _ H).
    * inversion H; inversion CVAL.
  Qed.

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    intro. intro. constructor; intro.
    * dependent induction H.
      - apply (bs_While_True _ _ _ c').
        assumption. apply EQ. assumption.
        apply (IHbs_int2 _ s1). assumption. reflexivity.
      - constructor. assumption.
    * dependent induction H.
      - apply (bs_While_True _ _ _ c').
        assumption. apply EQ. assumption.
        apply (IHbs_int2 _ s2). assumption. reflexivity.
      - constructor. assumption.
  Qed.

  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. intro. apply (loop_false _ _ _ H). Qed.

End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
    intro. intro. constructor; intro; dependent destruction H.
    * apply (bs_Seq _ c'). assumption. apply EQ. assumption.
    * apply (bs_Seq _ c'). assumption. apply EQ. assumption.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
    intro. intro. constructor; intro; dependent destruction H.
    * apply (bs_Seq _ c'). apply EQ. assumption. assumption.
    * apply (bs_Seq _ c'). apply EQ. assumption. assumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s ELSE s1 END ~~~ COND e THEN s ELSE s2 END.
Proof.
    intro. intro. constructor; intro; dependent destruction H.
    * apply bs_If_True. assumption. assumption.
    * apply bs_If_False. assumption. apply EQ. assumption.
    * apply bs_If_True. assumption. assumption.
    * apply bs_If_False. assumption. apply EQ. assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
    intro. intro. constructor; intro; dependent destruction H.
    * apply bs_If_True. assumption. apply EQ. assumption.
    * apply bs_If_False. assumption. assumption.
    * apply bs_If_True. assumption. apply EQ. assumption.
    * apply bs_If_False. assumption. assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
    intro. intro. constructor; intro; dependent induction H.
    * apply (bs_While_True _ _ _ c'). assumption. apply EQ. assumption.
      apply (IHbs_int2 e s1). assumption. reflexivity.
    * apply bs_While_False. assumption.
    * apply (bs_While_True _ _ _ c'). assumption. apply EQ. assumption.
      apply (IHbs_int2 e s2). assumption. reflexivity.
    * apply bs_While_False. assumption.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
    constructor. apply eq_congruence_seq_r. assumption.
    constructor. apply eq_congruence_seq_l. assumption.
    constructor. apply eq_congruence_cond_else. assumption.
    constructor. apply eq_congruence_cond_then. assumption.
    apply eq_congruence_while. assumption.
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
    try reflexivity; try by_eval_deterministic.

    all: try ( apply IHEXEC1_2; rewrite (IHEXEC1_1 c'0); assumption; assumption ).
    all: try ( apply IHEXEC1; assumption ).

    all: try ( absurd (Z.one = Z.zero);
        [ intro; inversion H
        | ( try rename s into st ); apply (eval_deterministic e st);
          try assumption; try assumption
        ] ).
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
(*
Lemma eq_c : ((Id 0 ::= Nat Z.zero) ;; (Id 0 ::= Nat Z.one)) ~c~
              (Id 0 ::= (Nat Z.one)).
Proof.
  unfold contextual_equivalent.
  intro C.
  unfold eval_equivalent.
  intros i o. split; intro H.
  { generalize dependent o. induction C; intros o H.
    { simpl in *. inversion H. inversion H0. subst. inversion STEP1. subst.
      unfold update in STEP2. simpl in STEP2. inversion STEP2. subst.
      econstructor. constructor. constructor.
    }
    { simpl in *. inversion_clear H. inversion_clear H0. destruct c', p.
      specialize (IHC l).
      assert (A: <| C <~ (Id 0 ::= Nat Z.zero) ;; (Id 0 ::= Nat Z.one) |> i => l

Lemma eq_eq_ceq s1 s2: s1 ~~~ s2 <-> s1 ~c~ s2.
Proof.
  split; intro H.
  { admit. }
  { unfold contextual_equivalent in H. unfold bs_equivalent. unfold eval_equivalent in H.
    intros c c'. split; intro Hbs.
    simpl in H. destruct c, c', p, p0.
    specialize (H l1 l0). inversion H.
 *)

Lemma eq_forall_context s1 s2 C (H : s1 ~~~ s2) : (C <~ s1) ~~~ (C <~ s2).
Proof.
    dependent induction C; try specialize (IHC H).
    * assumption.
    * constructor; intro; dependent destruction H0.
      all: try by econstructor; [ apply IHC; eassumption | assumption ].
    * constructor; intro; dependent destruction H0.
      all: try by econstructor; [ eassumption | apply IHC; assumption ].
    * constructor; intro; dependent destruction H0.
      all: try by apply bs_If_True; [ | apply IHC ].
      all: try by apply bs_If_False; assumption; assumption.
    * constructor; intro; dependent destruction H0.
      all: try by apply bs_If_True; assumption; assumption.
      all: try by apply bs_If_False; [ | apply IHC ].
    * constructor; intro; dependent induction H0.
      all: try by eapply bs_While_False; assumption.
      all: eapply bs_While_True;
        [ assumption
        | apply IHC; eassumption
        | eapply IHbs_int2; try eassumption; reflexivity
        ].
Qed.

Lemma extra_input_lem s st st' i i' o o' (H : (st, i, o) == s ==> (st', i', o'))
    : forall i'', (st, i ++ i'', o) == s ==> (st', i' ++ i'', o').
Proof.
    dependent induction H; intro.
    * constructor.
    * constructor. assumption.
    * constructor.
    * constructor. assumption.
    * destruct c' as ((st'', i'''), o'').
      specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl).
      specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl).
      econstructor. apply IHbs_int1. apply IHbs_int2.
    * specialize (IHbs_int _ _ _ _ _ _ JMeq_refl JMeq_refl).
      apply bs_If_True. assumption. apply IHbs_int.
    * specialize (IHbs_int _ _ _ _ _ _ JMeq_refl JMeq_refl).
      apply bs_If_False. assumption. apply IHbs_int.
    * destruct c' as ((st'', i'''), o'').
      specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl).
      specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl).
      eapply bs_While_True. assumption. apply IHbs_int1. apply IHbs_int2.
    * eapply bs_While_False. assumption.
Qed.

Lemma extra_input s st st' i i' o o' : ((st, i, o) == s ==> (st', i', o')
    <-> exists i'', i = i'' ++ i' /\ (st, i'', o) == s ==> (st', [], o')).
Proof.
    constructor; intro.
    * dependent induction H.
      - exists []. constructor; constructor.
      - exists []. constructor; constructor. assumption.
      - exists [z]. constructor; constructor.
      - exists []. constructor; constructor. assumption.
      - destruct c' as ((st'', i''), o'').
        specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl).
        specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl).
        destruct IHbs_int1, H1, IHbs_int2, H3.
        exists (x ++ x0). constructor.
        + rewrite <- app_assoc, H1, H3. reflexivity.
        + econstructor. apply extra_input_lem. eassumption. assumption.
      - specialize (IHbs_int _ _ _ _ _ _ JMeq_refl JMeq_refl). destruct IHbs_int, H0.
        exists x. constructor. assumption. apply bs_If_True; assumption.
      - specialize (IHbs_int _ _ _ _ _ _ JMeq_refl JMeq_refl). destruct IHbs_int, H0.
        exists x. constructor. assumption. apply bs_If_False; assumption.
      - destruct c' as ((st'', i''), o'').
        specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl).
        specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl).
        destruct IHbs_int1, H1, IHbs_int2, H3.
        exists (x ++ x0). constructor.
        + rewrite <- app_assoc, H1, H3. reflexivity.
        + eapply bs_While_True. assumption. apply extra_input_lem. eassumption. eassumption.
      - exists []. constructor; constructor. assumption.
    * dependent destruction H. dependent destruction H. rewrite H.
      eapply (extra_input_lem _ _ _ _ _ _ _ H0).
Qed.

Lemma extra_output_lem s st st' i i' o o' (H : (st, i, o) == s ==> (st', i', o'))
    : forall o'', (st, i, o ++ o'') == s ==> (st', i', o' ++ o'').
Proof.
    dependent induction H; intro.
    * constructor.
    * constructor. assumption.
    * constructor.
    * constructor. assumption.
    * destruct c' as ((st'', i''), o''').
      specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl).
      specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl).
      econstructor. apply IHbs_int1. apply IHbs_int2.
    * specialize (IHbs_int _ _ _ _ _ _ JMeq_refl JMeq_refl).
      apply bs_If_True. assumption. apply IHbs_int.
    * specialize (IHbs_int _ _ _ _ _ _ JMeq_refl JMeq_refl).
      apply bs_If_False. assumption. apply IHbs_int.
    * destruct c' as ((st'', i''), o''').
      specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl).
      specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl).
      eapply bs_While_True. assumption. apply IHbs_int1. apply IHbs_int2.
    * eapply bs_While_False. assumption.
Qed.

Lemma extra_output s st st' i i' o o' : ((st, i, o) == s ==> (st', i', o')
    <-> exists o'', o' = o'' ++ o /\ (st, i, []) == s ==> (st', i', o'')).
Proof.
    constructor; intro.
    * dependent induction H.
      - exists []. constructor; constructor.
      - exists []. constructor; constructor. assumption.
      - exists []. constructor; constructor.
      - exists [z]. constructor; constructor. assumption.
      - destruct c' as ((st'', i''), o'').
        specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl).
        specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl).
        destruct IHbs_int1, H1, IHbs_int2, H3.
        exists (x0 ++ x). constructor.
        + rewrite <- app_assoc, H3, H1. reflexivity.
        + econstructor. eassumption. apply (extra_output_lem _ _ _ _ _ _ _ H4).
      - specialize (IHbs_int _ _ _ _ _ _ JMeq_refl JMeq_refl). destruct IHbs_int, H0.
        exists x. constructor. assumption. apply bs_If_True; assumption.
      - specialize (IHbs_int _ _ _ _ _ _ JMeq_refl JMeq_refl). destruct IHbs_int, H0.
        exists x. constructor. assumption. apply bs_If_False; assumption.
      - destruct c' as ((st'', i''), o'').
        specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl).
        specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl).
        destruct IHbs_int1, H1, IHbs_int2, H3.
        exists (x0 ++ x). constructor.
        + rewrite <- app_assoc, H3, H1. reflexivity.
        + eapply bs_While_True. assumption. eassumption. apply (extra_output_lem _ _ _ _ _ _ _ H4).
      - exists []. constructor; constructor. assumption.
    * dependent destruction H. dependent destruction H. rewrite H.
      eapply (extra_output_lem _ _ _ _ _ _ _ H0).
Qed.

Fixpoint populating_context (st : state Z) : Context :=
match st with
| [] => Hole
| (v, x) :: st => SeqR (v ::= Nat x) (populating_context st)
end.

Lemma extra_state_lem s st st1 st' i i' o o' : (rev st ++ st1, i, o) == s ==> (st', i', o')
    <-> (st1, i, o) == populating_context st <~ s ==> (st', i', o').
Proof.
    dependent induction st.
    * constructor; auto.
    * destruct a as (v, x). simpl. constructor; intro.
      - econstructor. constructor. constructor. eapply IHst. rewrite <- app_assoc in H. apply H.
      - rewrite <- app_assoc. dependent destruction H. dependent destruction H.
        dependent destruction VAL. eapply IHst. assumption.
Qed.

Lemma extra_state s st st' i i' o o' : (st, i, o) == s ==> (st', i', o')
    <-> ([], i, o) == populating_context (rev st) <~ s ==> (st', i', o').
Proof.
    specialize (extra_state_lem s (rev st) nil). intro.
    rewrite app_nil_r, rev_involutive in H. apply H.
Qed.

Fixpoint dump_context (st : state Z) : Context :=
match st with
| [] => Hole
| (v, _) :: st => SeqL (dump_context st) (WRITE (Var v))
end.

Fixpoint state_dump_ex (st : state Z) (f : id -> Z) : list Z :=
match st with
| [] => []
| (v, x) :: st => f v :: state_dump_ex st f
end.

Fixpoint lookup_state (st : state Z) (v : id) : Z :=
match st with
| [] => 0
| (v', x) :: st => if id_eq_dec v v' then x else lookup_state st v
end.

Definition state_dump (st st' : state Z) : list Z := state_dump_ex st (lookup_state (st' ++ st)).

Lemma state_expands s st st' i i' o o' (H : (st, i, o) == s ==> (st', i', o'))
                                : exists st'', st' = st'' ++ st.
Proof.
    dependent induction H.

    all: try by exists []; reflexivity.
    all: try by exists [(x, z)]; reflexivity.
    all: try by specialize (IHbs_int _ _ _ _ _ _ JMeq_refl JMeq_refl); assumption.

    * destruct c' as ((st'', i''), o'').
      specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl). destruct IHbs_int1.
      specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl). destruct IHbs_int2.
      exists (x0 ++ x). rewrite H2, H1. apply app_assoc.
    * destruct c' as ((st'', i''), o'').
      specialize (IHbs_int1 _ _ _ _ _ _ JMeq_refl JMeq_refl). destruct IHbs_int1.
      specialize (IHbs_int2 _ _ _ _ _ _ JMeq_refl JMeq_refl). destruct IHbs_int2.
      exists (x0 ++ x). rewrite H2, H1. apply app_assoc.
Qed.

Lemma lookup_state_lem st1 st2 v x
    : (st1 ++ (v, x) :: st2) / v => (lookup_state (st1 ++ (v, x) :: st2) v).
Proof.
    dependent induction st1.
    * simpl. destruct (id_eq_dec v v).
      - constructor.
      - absurd (v = v); auto.
    * destruct a as (v', x'). simpl. destruct (id_eq_dec v v').
      - rewrite e. constructor.
      - constructor. assumption. apply IHst1; reflexivity.
Qed.

Lemma state_dump_context1 s st st' st1 i i' o o'
        (H : (st, i, o) == s ==> (st1 ++ st', i', o'))
    : exists st'', (forall v x, (st1 ++ st') / v => x -> st'' / v => x)
        /\ (st, i, o) == dump_context st' <~ s ==> (st'', i', state_dump st' st1 ++ o').
Proof.
    dependent induction st'.
    * specialize (state_expands _ _ _ _ _ _ _ H). intro. destruct H0.
      rewrite app_nil_r in H0, H. rewrite H0 in H. simpl. exists (x ++ st). constructor.
      - intros. rewrite <- H0. rewrite app_nil_r in H1. assumption.
      - assumption.
    * destruct a as (v, x). simpl. specialize (IHst' (st1 ++ [(v, x)])).
      rewrite <- app_assoc in IHst'. apply IHst' in H.
      destruct H, H. exists x0. constructor.
      - intros v' x' H'. apply H. assumption.
      - econstructor. eassumption.
        replace (state_dump st' (st1 ++ [(v, x)]))
        with (state_dump_ex st' (lookup_state ((st1 ++ [(v, x)]) ++ st'))).
        ** rewrite <- app_assoc. apply bs_Write. constructor. apply H. apply lookup_state_lem.
        ** reflexivity.
Qed.

Lemma state_dump_context2 s st' st1 i i' o o'
        (H : exists st'', ([], i, o) == dump_context st' <~ s ==> (st'', i', state_dump st' st1 ++ o'))
    : ([], i, o) == s ==> (st1 ++ st', i', o').
Proof.
    dependent induction st'.
    * destruct H. simpl in H. rewrite app_nil_r. admit.
    * destruct a as (v, x). specialize (IHst' _ Logic.eq_refl JMeq_refl (st1 ++ [(v, x)])).
      rewrite <- app_assoc in IHst'. apply IHst'. destruct H. simpl in H. dependent destruction H.
      dependent destruction H0. exists x0.
      replace (state_dump st' (st1 ++ [(v, x)]))
      with (state_dump_ex st' (lookup_state ((st1 ++ [(v, x)]) ++ st'))).
      - rewrite <- app_assoc. assumption.
      - reflexivity.
Admitted.

Lemma state_dump_context s st' i i' o o' : ([], i, o) == s ==> (st', i', o')
    <-> exists st'', ([], i, o) == dump_context st' <~ s ==> (st'', i', state_dump st' nil ++ o').
Proof.
    constructor; intro.
    * apply (state_dump_context1 _ _ _ nil) in H. destruct H, H. exists x. assumption.
    * apply (state_dump_context2 _ _ nil). assumption.
Qed.

Fixpoint plug_context (C C' : Context) : Context :=
match C with
| Hole => C'
| SeqL     C  s1 => SeqL (plug_context C C') s1
| SeqR     s1 C  => SeqR s1 (plug_context C C')
| IfThen e C  s1 => IfThen e (plug_context C C') s1
| IfElse e s1 C  => IfElse e s1 (plug_context C C')
| WhileC   e  C  => WhileC e (plug_context C C')
end.

Notation "C '<C~' C'" := (plug_context C C') (at level 43, no associativity).

Lemma plug_context_plug C C' s : C <~ (C' <~ s) = C <C~ C' <~ s.
Proof. dependent induction C; simpl; congruence. Qed.

Lemma eq_eq_ceq s1 s2 : s1 ~~~ s2 <-> s1 ~c~ s2.
Proof.
    constructor; intro.
    * constructor; intro; dependent destruction H0; econstructor.
      - eapply eq_forall_context.
        + intros c c'. symmetry. eapply H.
        + eassumption.
      - eapply eq_forall_context. eassumption. eassumption.
    * constructor; intro; destruct c as ((st, i), o), c' as ((st', o'), i').
      - apply extra_input in H0. destruct H0, H0.
        apply extra_input. exists x. constructor. assumption.
        apply extra_output in H1. destruct H1, H1.
        apply extra_output. exists x0. constructor. assumption.
        apply extra_state in H2.
        apply extra_state.
        apply state_dump_context in H2. rewrite plug_context_plug in H2.
        apply state_dump_context. rewrite plug_context_plug.
        apply H. apply H2.
      - apply extra_input in H0. destruct H0, H0.
        apply extra_input. exists x. constructor. assumption.
        apply extra_output in H1. destruct H1, H1.
        apply extra_output. exists x0. constructor. assumption.
        apply extra_state in H2.
        apply extra_state.
        apply state_dump_context in H2. rewrite plug_context_plug in H2.
        apply state_dump_context. rewrite plug_context_plug.
        apply H. apply H2.
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
    dependent induction s;
    dependent destruction EXEC1; dependent destruction EXEC2.

    all: try reflexivity.
    all: try by_eval_deterministic.
    all: try by dependent destruction EXEC1; dependent destruction EXEC2.
    all: try by specialize (IHs1 _ _ _ EXEC1 EXEC2); inversion IHs1; f_equal.
    all: absurd (Z.one = Z.zero);
        [ intro; inversion H
        | apply (eval_deterministic e s); assumption; assumption
        ].
  Qed.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    dependent induction STEP1; dependent destruction STEP2.
    * remember (ss_int_step_deterministic _ _ _ _ H H0). inversion e. reflexivity.
    * absurd (Some s' = None).
      - intro. inversion H1.
      - remember (ss_int_step_deterministic _ _ _ _ H H0). inversion e.
    * absurd (Some s' = None).
      - intro. inversion H1.
      - remember (ss_int_step_deterministic _ _ _ _ H H0). inversion e.
    * remember (ss_int_step_deterministic _ _ _ _ H H0). inversion e.
      apply IHSTEP1. rewrite H2, H3. assumption.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. dependent destruction STEP; constructor; try assumption. Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'.
  Proof.
    dependent induction STEP1.
    * apply (ss_int_Step _ s2 _ c'0). constructor. assumption. assumption.
    * apply (ss_int_Step _ (s' ;; s2) _ c'0). constructor. assumption.
      apply IHSTEP1. assumption.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    dependent induction s generalizing c c' c''; dependent destruction STEP.
    * apply (bs_Seq _ c'). apply ss_bs_base. assumption. assumption.
    * dependent destruction EXEC. apply (bs_Seq _ c').
      apply (IHs1 _ _ _ _ STEP). assumption. assumption.
    * apply bs_If_True. assumption. assumption.
    * apply bs_If_False. assumption. assumption.
    * apply SmokeTest.while_unfolds. assumption.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    constructor; intros.
    * dependent induction H.

      all: try by constructor; constructor; try assumption.
      all: try by dependent destruction IHbs_int; econstructor; econstructor; eassumption.

      - apply (ss_ss_composition _ _ _ _ _ IHbs_int1 IHbs_int2).
      - dependent destruction IHbs_int1.
        + apply (ss_int_Step _ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) _ (st, i, o)).
          apply ss_While. apply (ss_int_Step _ (s ;; WHILE e DO s END) _ (st, i, o) _).
          apply ss_If_True. assumption. apply (ss_int_Step _ (WHILE e DO s END) _ c' _).
          apply ss_Seq_Compl. assumption. assumption.
        + apply (ss_int_Step _ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) _ (st, i, o)).
          apply ss_While. apply (ss_int_Step _ (s ;; WHILE e DO s END) _ (st, i, o) _).
          apply ss_If_True. assumption. apply (ss_int_Step _ (s' ;; WHILE e DO s END) _ c' _).
          apply ss_Seq_InCompl. assumption. apply (ss_ss_composition _ _ c''0). assumption.
          assumption.
      - apply (ss_int_Step _ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) _ (st, i, o)).
        apply ss_While. apply (ss_int_Step _ SKIP _ (st, i, o)). constructor. assumption.
        constructor. constructor.
    * dependent induction H.
      - dependent destruction H; constructor; try assumption.
      - eapply ss_bs_step. eassumption. eassumption.
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

  Lemma re_rename_conf
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (c    : conf) : rename_conf r (rename_conf r' c) = c.
  Proof. destruct c as ((st, i), o). simpl. rewrite Renaming.re_rename_state; auto. Qed.

  Lemma re_rename
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (s    : stmt) : rename r (rename r' s) = s.
  Proof. dependent induction s; simpl; try rewrite Renaming.re_rename_expr; congruence. Qed.

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. dependent destruction r. constructor. Qed.

  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant' s r c c' (H : c == s ==> c')
    : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r, b, a. dependent induction H.
    * constructor.
    * constructor. rewrite <- Renaming.eval_renaming_invariance. assumption.
    * constructor.
    * constructor. rewrite <- Renaming.eval_renaming_invariance. assumption.
    * econstructor; eassumption.
    * eapply bs_If_True. apply Renaming.eval_renaming_invariance. assumption. assumption.
    * eapply bs_If_False. apply Renaming.eval_renaming_invariance. assumption. assumption.
    * eapply bs_While_True.
      - apply Renaming.eval_renaming_invariance. assumption.
      - eassumption.
      - eassumption.
    * eapply bs_While_False. apply Renaming.eval_renaming_invariance. assumption.
  Qed.

  Lemma renaming_invariant'' s r c c'
    : c == s ==> c' <-> (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    constructor; intro.
    * apply renaming_invariant'. assumption.
    * set (r' := Renaming.renaming_inv r). destruct r' as [r' Hinv].
      erewrite <- (re_rename _ _ Hinv s).
      erewrite <- (re_rename_conf _ _ Hinv c).
      erewrite <- (re_rename_conf _ _ Hinv c').
      apply renaming_invariant'. eassumption.
  Qed.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof. apply renaming_invariant''. assumption. Qed.

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof. apply renaming_invariant'' in Hbs. assumption. Qed.

  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    constructor; intro.
    * destruct H. econstructor.
      specialize (renaming_invariant' s r ([], i, []) (x, [], o)). intro.
      specialize (H0 H). destruct r, b, a. simpl in H0. eassumption.
    * set (r' := Renaming.renaming_inv r). destruct r' as [r' Hinv]. destruct H as [st].
      specialize (renaming_invariant'' s r ([], i, []) (rename_conf r' (st, [], o))). intro.
      destruct H0. rewrite re_rename_conf in H1. specialize (H1 H).
      econstructor. apply H1. apply Renaming.renamings_symm. assumption.
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

Lemma Kapp_neutral_left (k : cont) : (KEmpty @ k) = k.
Proof. dependent destruction k; reflexivity. Qed.

Lemma Kapp_neutral_right (k : cont) : (k @ KEmpty) = k.
Proof. dependent destruction k; reflexivity. Qed.

Ltac cps_bs_gen_helper k H HH :=
  destruct k eqn:K; subst; inversion H; subst;
  [inversion EXEC; subst | eapply bs_Seq; eauto];
  apply HH; auto.

Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof.
    dependent induction EXEC generalizing S.

    dependent destruction DEF.
    all: try by dependent destruction k; dependent destruction DEF;
        [ dependent destruction EXEC; econstructor
        | econstructor; [ constructor | apply IHEXEC; reflexivity ]
        ].

    * dependent destruction k; dependent destruction DEF.
      - apply IHEXEC. reflexivity.
      - apply SmokeTest.seq_assoc. apply IHEXEC. reflexivity.
    * dependent destruction k; dependent destruction DEF.
      - apply bs_If_True. assumption. apply IHEXEC. reflexivity.
      - assert (H : (s, i, o) == s1 ;; s0 ==> c').
        + apply IHEXEC. reflexivity.
        + dependent destruction H. apply (bs_Seq _ c'). apply bs_If_True.
          assumption. assumption. assumption.
    * dependent destruction k; dependent destruction DEF.
      - apply bs_If_False. assumption. apply IHEXEC. reflexivity.
      - assert (H : (s, i, o) == s2 ;; s0 ==> c').
        + apply IHEXEC. reflexivity.
        + dependent destruction H. apply (bs_Seq _ c'). apply bs_If_False.
          assumption. assumption. assumption.
    * dependent destruction k; dependent destruction DEF.
      - assert (H : (st, i, o) == s ;; WHILE e DO s END ==> c').
        + apply IHEXEC. reflexivity.
        + dependent destruction H. apply (bs_While_True _ _ _ c').
          assumption. assumption. assumption.
      - assert (H : (st, i, o) == s0 ;; (WHILE e DO s0 END ;; s) ==> c').
        + apply IHEXEC. reflexivity.
        + dependent destruction H. dependent destruction H0.
          apply (bs_Seq _ c'). apply (bs_While_True _ _ _ c). assumption. assumption.
          assumption. assumption.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. apply (cps_bs_gen _ _ _ !s1 !s2). assumption. reflexivity. Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') :
  c == s ==> c'.
Proof. apply (cps_bs_gen _ _ _ !s KEmpty). assumption. reflexivity. Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
    dependent induction STEP; dependent destruction k2.

    all: try by econstructor; try econstructor; eassumption; try eassumption.

    all: try by assert (H : k3 = KEmpty);
        [ dependent destruction k3; try auto; try inversion x
        | dependent destruction H; try constructor
        ].
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
    dependent induction EXEC generalizing k.

    assumption.
    all: try by dependent destruction STEP; econstructor; try econstructor; try eassumption.
    all: try by econstructor; [ eassumption | apply IHEXEC; assumption ].

    * constructor. apply IHEXEC1. constructor. apply cps_cont_to_seq. apply IHEXEC2.
      rewrite Kapp_neutral_right. assumption.
    * apply cps_While_True. assumption. apply IHEXEC1. constructor. apply cps_cont_to_seq.
      apply IHEXEC2. rewrite Kapp_neutral_right. assumption.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. apply (bs_int_to_cps_int_cont _ c'). assumption. constructor. constructor. Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
