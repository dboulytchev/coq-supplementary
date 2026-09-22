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
  exact H.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists ((Id 0) ::= Nat 1), ((Id 0) ::= Nat 2).
  split.
  - unfold eval_equivalent, eval. intros i o. split; intro H.
    + destruct H as [st H]. inversion H; subst.
      exists [(Id 0, 2%Z)]. apply bs_Assign. constructor.
    + destruct H as [st H]. inversion H; subst.
      exists [(Id 0, 1%Z)]. apply bs_Assign. constructor.
  - intro Hc.
    specialize (Hc (SeqL Hole (WRITE (Var (Id 0))))).
    unfold eval_equivalent, eval in Hc.
    simpl in Hc.
    destruct (Hc nil (1%Z :: nil)) as [Hc1 Hc2].
    assert (H1 : exists st, ([],[],[]) == (((Id 0)::=Nat 1);;WRITE(Var(Id 0))) ==> (st,[],[1%Z])).
    { exists [(Id 0,1%Z)]. eapply bs_Seq.
      - apply bs_Assign. constructor.
      - apply bs_Write. constructor. constructor. }
    apply Hc1 in H1.
    destruct H1 as [st2 H1].
    inversion H1; subst.
    match goal with
    | HA : (_, _, _) == ((Id 0) ::= Nat 2) ==> _ |- _ => inversion HA; subst
    end.
    match goal with
    | HN : [| Nat 2 |] _ => _ |- _ => inversion HN; subst
    end.
    match goal with
    | HW : (_, _, _) == WRITE (Var (Id 0)) ==> _ |- _ => inversion HW; subst
    end.
    match goal with
    | HV : [| Var (Id 0) |] _ => _ |- _ => inversion HV; subst
    end.
    match goal with
    | HB : _ / (Id 0) => _ |- _ => inversion HB; subst
    end.
    match goal with H : ?a <> ?a |- _ => exfalso; apply H; reflexivity end.
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
    intros c c'. split; intro H.
    - inversion H; subst.
      match goal with
      | H1 : _ == (s1 ;; s2) ==> _ |- _ => inversion H1; subst
      end.
      eapply bs_Seq; [eassumption | eapply bs_Seq; eassumption].
    - inversion H; subst.
      match goal with
      | H2 : _ == (s2 ;; s3) ==> _ |- _ => inversion H2; subst
      end.
      eapply bs_Seq; [eapply bs_Seq; eassumption | eassumption].
  Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    intros c c'. split; intro H.
    - inversion H; subst.
      + eapply bs_If_True; [assumption | eapply bs_Seq; eassumption].
      + eapply bs_If_False; [assumption | constructor].
    - inversion H; subst.
      + match goal with
        | HS : _ == (s ;; WHILE e DO s END) ==> _ |- _ => inversion HS; subst
        end.
        eapply bs_While_True; eassumption.
      + match goal with
        | HS : _ == SKIP ==> _ |- _ => inversion HS; subst
        end.
        constructor. assumption.
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as w eqn:Hw.
    remember (st, i, o) as cf eqn:Hcf.
    revert st i o Hcf Hw.
    induction EXE; intros st0 i0 o0 Hcf Hw; try discriminate Hw.
    - inversion Hw; subst.
      eapply IHEXE2; reflexivity.
    - inversion Hw; subst.
      inversion Hcf; subst.
      assumption.
  Qed.

  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro H.
    remember (WHILE (Nat 1) DO s END) as w eqn:Hw.
    revert Hw.
    induction H; intros Hw; try discriminate Hw.
    - inversion Hw; subst.
      match goal with
      | IH : WHILE (Nat 1) DO s END = WHILE (Nat 1) DO s END -> False |- _ =>
          apply IH; reflexivity
      end.
    - inversion Hw; subst.
      match goal with CVAL : [| Nat 1 |] _ => Z.zero |- _ => inversion CVAL end.
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    intros c c'. split; intro H.
    - exfalso. apply (while_true_undefined c SKIP c'). exact H.
    - exfalso. inversion H; subst.
      + match goal with CVAL : [| Nat 3 |] _ => Z.one |- _ => inversion CVAL end.
      + match goal with CVAL : [| Nat 3 |] _ => Z.zero |- _ => inversion CVAL end.
  Qed.

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent in *.
    intros c c'. split; intro H.
    - remember (WHILE e DO s1 END) as w eqn:Hw.
      revert Hw.
      induction H; intros Hw; try discriminate Hw.
      + inversion Hw; subst.
        eapply bs_While_True.
        * exact CVAL.
        * apply (proj1 (EQ _ _)). exact H.
        * apply IHbs_int2. reflexivity.
      + inversion Hw; subst.
        constructor. exact CVAL.
    - remember (WHILE e DO s2 END) as w eqn:Hw.
      revert Hw.
      induction H; intros Hw; try discriminate Hw.
      + inversion Hw; subst.
        eapply bs_While_True.
        * exact CVAL.
        * apply (proj2 (EQ _ _)). exact H.
        * apply IHbs_int2. reflexivity.
      + inversion Hw; subst.
        constructor. exact CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  intros c c'. split; intro H.
  - inversion H; subst. eapply bs_Seq; [eassumption | apply (proj1 (EQ _ _)); eassumption].
  - inversion H; subst. eapply bs_Seq; [eassumption | apply (proj2 (EQ _ _)); eassumption].
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  intros c c'. split; intro H.
  - inversion H; subst. eapply bs_Seq; [apply (proj1 (EQ _ _)); eassumption | eassumption].
  - inversion H; subst. eapply bs_Seq; [apply (proj2 (EQ _ _)); eassumption | eassumption].
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  intros c c'. split; intro H.
  - inversion H; subst.
    + apply bs_If_True; assumption.
    + apply bs_If_False; [assumption | apply (proj1 (EQ _ _)); assumption].
  - inversion H; subst.
    + apply bs_If_True; assumption.
    + apply bs_If_False; [assumption | apply (proj2 (EQ _ _)); assumption].
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  intros c c'. split; intro H.
  - inversion H; subst.
    + apply bs_If_True; [assumption | apply (proj1 (EQ _ _)); assumption].
    + apply bs_If_False; assumption.
  - inversion H; subst.
    + apply bs_If_True; [assumption | apply (proj2 (EQ _ _)); assumption].
    + apply bs_If_False; assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. exact (SmokeTest.while_eq e s1 s2 EQ). Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split.
  - apply eq_congruence_seq_r. exact EQ.
  - split.
    + apply eq_congruence_seq_l. exact EQ.
    + split.
      * apply eq_congruence_cond_else. exact EQ.
      * split.
        -- apply eq_congruence_cond_then. exact EQ.
        -- apply eq_congruence_while. exact EQ.
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
  induction EXEC1; intros c2 EXEC2; inversion EXEC2; subst.
  - reflexivity.
  - assert (z = z0) by (eapply eval_deterministic; eassumption). subst. reflexivity.
  - reflexivity.
  - assert (z = z0) by (eapply eval_deterministic; eassumption). subst. reflexivity.
  - match goal with
    | IH1 : forall c2, _ == s1 ==> c2 -> _, H1 : _ == s1 ==> ?cm |- _ =>
        assert (c' = cm) by (apply IH1; assumption); subst
    end.
    match goal with
    | IH2 : forall c2, _ == s2 ==> c2 -> _ |- _ => apply IH2; assumption
    end.
  - apply IHEXEC1. assumption.
  - eval_zero_not_one.
  - eval_zero_not_one.
  - apply IHEXEC1. assumption.
  - match goal with
    | IH1 : forall c2, (st, i, o) == s ==> c2 -> _, H1 : (st, i, o) == s ==> ?cm |- _ =>
        assert (c' = cm) by (apply IH1; assumption); subst
    end.
    match goal with
    | IH2 : forall c2, _ == WHILE e DO s END ==> c2 -> _ |- _ => apply IH2; assumption
    end.
  - eval_zero_not_one.
  - eval_zero_not_one.
  - reflexivity.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma equiv_states_update (s1 s2 : state Z) (HE : equivalent_states s1 s2) (x : id) (z : Z) :
  equivalent_states (s1 [x <- z]) (s2 [x <- z]).
Proof.
  unfold equivalent_states, Expr.equivalent_states in *.
  intros id0 z0.
  destruct (id_eq_dec x id0) as [Heq | Hneq].
  - subst.
    split; intro H0.
    + assert (z0 = z) by (eapply state_deterministic; [exact H0 | apply update_eq]).
      subst. apply update_eq.
    + assert (z0 = z) by (eapply state_deterministic; [exact H0 | apply update_eq]).
      subst. apply update_eq.
  - split; intro H0.
    + apply (proj1 (update_neq Z s2 x id0 z z0 Hneq)).
      apply (proj1 (HE id0 z0)).
      apply (proj2 (update_neq Z s1 x id0 z z0 Hneq)).
      exact H0.
    + apply (proj1 (update_neq Z s1 x id0 z z0 Hneq)).
      apply (proj2 (HE id0 z0)).
      apply (proj2 (update_neq Z s2 x id0 z z0 Hneq)).
      exact H0.
Qed.

Lemma bs_equiv_states_gen
  (s : stmt) (c1 c2 : conf) (st1' : state Z)
  (HE1 : equivalent_states (fst (fst c1)) st1')
  (H   : c1 == s ==> c2) :
  exists st2', equivalent_states (fst (fst c2)) st2' /\
    (st1', snd (fst c1), snd c1) == s ==> (st2', snd (fst c2), snd c2).
Proof.
  revert st1' HE1.
  induction H; intros st1' HE1; simpl in *.
  - exists st1'. split; [exact HE1 | constructor].
  - exists (st1' [x <- z]). split.
    + apply equiv_states_update. exact HE1.
    + constructor. apply (Expr.variable_relevance e s st1' z (fun id0 _ => HE1 id0)). exact VAL.
  - exists (st1' [x <- z]). split.
    + apply equiv_states_update. exact HE1.
    + constructor.
  - exists st1'. split.
    + exact HE1.
    + constructor. apply (Expr.variable_relevance e s st1' z (fun id0 _ => HE1 id0)). exact VAL.
  - destruct (IHbs_int1 st1' HE1) as [stm [HEm Hm]].
    destruct (IHbs_int2 stm HEm) as [st2' [HE2 H2]].
    exists st2'. split; [exact HE2 | eapply bs_Seq; eassumption].
  - destruct (IHbs_int st1' HE1) as [st2' [HE2 H2]].
    exists st2'. split.
    + exact HE2.
    + apply bs_If_True; [ apply (Expr.variable_relevance e s st1' Z.one (fun id0 _ => HE1 id0)); exact CVAL | exact H2 ].
  - destruct (IHbs_int st1' HE1) as [st2' [HE2 H2]].
    exists st2'. split.
    + exact HE2.
    + apply bs_If_False; [ apply (Expr.variable_relevance e s st1' Z.zero (fun id0 _ => HE1 id0)); exact CVAL | exact H2 ].
  - destruct (IHbs_int1 st1' HE1) as [stm [HEm Hm]].
    destruct (IHbs_int2 stm HEm) as [st2' [HE2 H2]].
    exists st2'. split.
    + exact HE2.
    + eapply bs_While_True; [ apply (Expr.variable_relevance e st st1' Z.one (fun id0 _ => HE1 id0)); exact CVAL | exact Hm | exact H2 ].
  - exists st1'. split.
    + exact HE1.
    + apply bs_While_False. apply (Expr.variable_relevance e st st1' Z.zero (fun id0 _ => HE1 id0)). exact CVAL.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  exact (bs_equiv_states_gen s (st1, i, o) (st2, i', o') st1' HE1 H).
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
    induction EXEC1; intros c'' EXEC2; inversion EXEC2; subst.
    - reflexivity.
    - assert (z = z0) by (eapply eval_deterministic; eassumption). subst. reflexivity.
    - reflexivity.
    - assert (z = z0) by (eapply eval_deterministic; eassumption). subst. reflexivity.
    - match goal with
      | HH : _ -- s1 --> (None, _) |- _ =>
          assert (Heq := IHEXEC1 _ HH); inversion Heq; subst
      end.
      reflexivity.
    - exfalso.
      match goal with
      | HH : _ -- s1 --> (Some _, _) |- _ => discriminate (IHEXEC1 _ HH)
      end.
    - exfalso.
      match goal with
      | HH : _ -- s1 --> (None, _) |- _ => discriminate (IHEXEC1 _ HH)
      end.
    - match goal with
      | HH : _ -- s1 --> (Some _, _) |- _ =>
          pose proof (IHEXEC1 _ HH) as Heq; inversion Heq; subst
      end.
      reflexivity.
    - reflexivity.
    - eval_zero_not_one.
    - eval_zero_not_one.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    revert c'' STEP2.
    induction STEP1; intros fin STEP2; inversion STEP2; subst.
    - match goal with
      | H1 : c -- s --> (None, _), H2 : c -- s --> (None, _) |- _ =>
          assert (Heq := ss_int_step_deterministic s c _ _ H1 H2); inversion Heq; subst; reflexivity
      end.
    - exfalso.
      match goal with
      | H1 : c -- s --> (None, _), H2 : c -- s --> (Some _, _) |- _ =>
          assert (Heq := ss_int_step_deterministic s c _ _ H1 H2); discriminate Heq
      end.
    - exfalso.
      match goal with
      | H1 : c -- s --> (Some _, _), H2 : c -- s --> (None, _) |- _ =>
          assert (Heq := ss_int_step_deterministic s c _ _ H1 H2); discriminate Heq
      end.
    - match goal with
      | H1 : c -- s --> (Some _, _), H2 : c -- s --> (Some _, _) |- _ =>
          assert (Heq := ss_int_step_deterministic s c _ _ H1 H2); inversion Heq; subst
      end.
      apply IHSTEP1. assumption.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP; subst.
    - constructor.
    - constructor. assumption.
    - constructor.
    - constructor. assumption.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'.
  Proof.
    revert c' STEP2.
    induction STEP1; intros c'0 STEP2.
    - eapply ss_int_Step.
      + apply ss_Seq_Compl. eassumption.
      + exact STEP2.
    - eapply ss_int_Step.
      + apply ss_Seq_InCompl. eassumption.
      + apply IHSTEP1. exact STEP2.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    remember (Some s', c') as r eqn:Hr.
    revert s' c' Hr c'' EXEC.
    induction STEP; intros s'0 c'0 Hr c''0 EXEC; try discriminate Hr; inversion Hr; subst.
    - eapply bs_Seq; [apply ss_bs_base; eassumption | exact EXEC].
    - inversion EXEC; subst.
      match goal with
      | H1 : _ == s1' ==> ?cm, H2 : ?cm == _ ==> _ |- _ =>
          eapply bs_Seq; [eapply IHSTEP; [reflexivity | exact H1] | exact H2]
      end.
    - apply bs_If_True; assumption.
    - apply bs_If_False; assumption.
    - destruct c'0 as [[st i] o].
      inversion EXEC; subst.
      + match goal with
        | HS : (st, i, o) == (s ;; WHILE e DO s END) ==> _ |- _ => inversion HS; subst
        end.
        eapply bs_While_True; eassumption.
      + match goal with
        | HS : (st, i, o) == SKIP ==> _ |- _ => inversion HS; subst
        end.
        apply bs_While_False. assumption.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intro H.
    - induction H.
      + apply ss_int_Base. constructor.
      + apply ss_int_Base. constructor. assumption.
      + apply ss_int_Base. constructor.
      + apply ss_int_Base. constructor. assumption.
      + eapply ss_ss_composition; eassumption.
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
          -- eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          -- apply ss_If_False. assumption.
          -- apply ss_int_Base. constructor.
    - induction H.
      + apply ss_bs_base. assumption.
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
    induction s; simpl.
    - reflexivity.
    - f_equal; [apply Hinv | apply Renaming.re_rename_expr; exact Hinv].
    - f_equal. apply Hinv.
    - f_equal. apply Renaming.re_rename_expr. exact Hinv.
    - f_equal; assumption.
    - f_equal; [apply Renaming.re_rename_expr; exact Hinv | assumption | assumption].
    - f_equal; [apply Renaming.re_rename_expr; exact Hinv | assumption].
  Qed.

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    destruct r as [f Hbij]. simpl. reflexivity.
  Qed.

  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    induction Hbs.
    - simpl. constructor.
    - unfold rename_conf. rewrite rename_state_update_permute. simpl. constructor. apply Renaming.eval_renaming_invariance. assumption.
    - unfold rename_conf. rewrite rename_state_update_permute. simpl. constructor.
    - simpl. constructor. apply Renaming.eval_renaming_invariance. assumption.
    - eapply bs_Seq; eassumption.
    - apply bs_If_True; [apply Renaming.eval_renaming_invariance; assumption | assumption].
    - apply bs_If_False; [apply Renaming.eval_renaming_invariance; assumption | assumption].
    - eapply bs_While_True; [apply Renaming.eval_renaming_invariance; assumption | eassumption | eassumption].
    - apply bs_While_False. apply Renaming.eval_renaming_invariance. assumption.
  Qed.

  Lemma re_rename_conf (r r' : Renaming.renaming) (Hinv : Renaming.renamings_inv r' r) (c : conf) :
    rename_conf r' (rename_conf r c) = c.
  Proof.
    destruct c as [[st i] o]. simpl. f_equal. f_equal. apply Renaming.re_rename_state. exact Hinv.
  Qed.

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r) as [r' Hinv'].
    assert (H2 := renaming_invariant_bs (rename r s) r' (rename_conf r c) (rename_conf r c') Hbs).
    rewrite (re_rename r' r Hinv') in H2.
    rewrite (re_rename_conf r r' Hinv' c) in H2.
    rewrite (re_rename_conf r r' Hinv' c') in H2.
    exact H2.
  Qed.

  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent, eval. intros i o. split; intro H.
    - destruct H as [st H].
      exists (Renaming.rename_state r st).
      assert (H2 := renaming_invariant_bs s r ([],i,[]) (st,[],o) H).
      simpl in H2. exact H2.
    - destruct H as [st H].
      destruct (Renaming.renaming_inv2 r) as [r' Hinv'].
      exists (Renaming.rename_state r' st).
      apply (renaming_invariant_bs_inv s r ([],i,[]) (Renaming.rename_state r' st, [], o)).
      simpl.
      rewrite (Renaming.re_rename_state r r' Hinv' st).
      exact H.
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

Ltac debug_print_all :=
  (repeat match goal with Hh : ?T |- _ => idtac Hh ":" T; fail end) || idtac "---".

Ltac inv_seq_hyp :=
  match goal with
  | H2 : _ == (_ ;; _) ==> _ |- _ => inversion H2; subst
  end.

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
    
Lemma cps_bs_gen_aux (S1 k : cont) (c c' : conf) (EXEC : k |- c -- S1 --> c') :
  forall X, S1 = !X ->
  match k with
  | KEmpty => c == X ==> c'
  | KStmt ks => c == X ;; ks ==> c'
  end.
Proof.
  induction EXEC; intros X0 HS1; try discriminate HS1; inversion HS1; subst.
  - destruct k as [ | ks].
    + inversion EXEC; subst. constructor.
    + assert (IH2 := IHEXEC ks Logic.eq_refl). simpl in IH2. eapply bs_Seq; [constructor | exact IH2].
  - destruct k as [ | ks].
    + inversion EXEC; subst. constructor. assumption.
    + assert (IH2 := IHEXEC ks Logic.eq_refl). simpl in IH2. eapply bs_Seq; [eapply bs_Assign; exact CVAL | exact IH2].
  - destruct k as [ | ks].
    + inversion EXEC; subst. constructor.
    + assert (IH2 := IHEXEC ks Logic.eq_refl). simpl in IH2. eapply bs_Seq; [eapply bs_Read | exact IH2].
  - destruct k as [ | ks].
    + inversion EXEC; subst. constructor. assumption.
    + assert (IH2 := IHEXEC ks Logic.eq_refl). simpl in IH2. eapply bs_Seq; [eapply bs_Write; exact CVAL | exact IH2].
  - destruct k as [ | ks].
    + assert (IH2 := IHEXEC s1 Logic.eq_refl). simpl in IH2. exact IH2.
    + assert (IH2 := IHEXEC s1 Logic.eq_refl). simpl in IH2.
      apply (proj2 (SmokeTest.seq_assoc s1 s2 ks c c')). exact IH2.
  - destruct k as [ | ks].
    + assert (IH2 := IHEXEC s1 Logic.eq_refl). simpl in IH2. apply bs_If_True; assumption.
    + assert (IH2 := IHEXEC s1 Logic.eq_refl). simpl in IH2.
      inversion IH2; subst. eapply bs_Seq; [apply bs_If_True; eassumption | eassumption].
  - destruct k as [ | ks].
    + assert (IH2 := IHEXEC s2 Logic.eq_refl). simpl in IH2. apply bs_If_False; assumption.
    + assert (IH2 := IHEXEC s2 Logic.eq_refl). simpl in IH2.
      inversion IH2; subst. eapply bs_Seq; [apply bs_If_False; eassumption | eassumption].
  - destruct k as [ | ks].
    + assert (IH2 := IHEXEC s Logic.eq_refl). simpl in IH2.
      inversion IH2; subst. eapply bs_While_True; eassumption.
    + assert (IH2 := IHEXEC s Logic.eq_refl). simpl in IH2.
      inversion IH2; subst.
      inv_seq_hyp.
      eapply bs_Seq; [eapply bs_While_True; eassumption | eassumption].
  - destruct k as [ | ks].
    + inversion EXEC; subst. apply bs_While_False. assumption.
    + assert (IH2 := IHEXEC ks Logic.eq_refl). simpl in IH2.
      eapply bs_Seq; [apply bs_While_False; assumption | exact IH2].
Qed.

Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof.
  destruct S1 as [ | X].
  - simpl in DEF. inversion EXEC; subst. discriminate DEF.
  - destruct k as [ | ks].
    + simpl in DEF. injection DEF as DEF. subst.
      exact (cps_bs_gen_aux (!X) KEmpty c c' EXEC X Logic.eq_refl).
    + simpl in DEF. injection DEF as DEF. subst.
      exact (cps_bs_gen_aux (!X) (!ks) c c' EXEC X Logic.eq_refl).
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. exact (cps_bs_gen (s1 ;; s2) c c' (!s1) (!s2) STEP Logic.eq_refl). Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') :
  c == s ==> c'.
Proof. exact (cps_bs_gen s c c' (!s) KEmpty STEP Logic.eq_refl). Qed.

Lemma cps_cont_to_seq_gen (K k1 : cont) (c1 c2 : conf) (STEP : K |- c1 -- k1 --> c2) :
  forall k2 k3, K = k2 @ k3 -> k3 |- c1 -- k1 @ k2 --> c2.
Proof.
  induction STEP; intros k2 k3 Heq.
  - destruct k2 as [ | s2]; destruct k3 as [ | s3]; simpl in Heq; try discriminate Heq.
    simpl. constructor.
  - subst k. destruct k2 as [ | s2].
    + simpl in *. eapply cps_Skip. exact STEP.
    + simpl in *. eapply cps_Seq. eapply cps_Skip. exact STEP.
  - subst k. destruct k2 as [ | s2].
    + simpl in *. eapply cps_Assign; [exact CVAL | exact STEP].
    + simpl in *. eapply cps_Seq. eapply cps_Assign; [exact CVAL | exact STEP].
  - subst k. destruct k2 as [ | s2].
    + simpl in *. eapply cps_Read. exact STEP.
    + simpl in *. eapply cps_Seq. eapply cps_Read. exact STEP.
  - subst k. destruct k2 as [ | s2].
    + simpl in *. eapply cps_Write; [exact CVAL | exact STEP].
    + simpl in *. eapply cps_Seq. eapply cps_Write; [exact CVAL | exact STEP].
  - subst k. destruct k2 as [ | s2'].
    + simpl in *. eapply cps_Seq. exact STEP.
    + simpl in *. eapply cps_Seq. eapply cps_Seq. exact STEP.
  - subst k. destruct k2 as [ | s2'].
    + simpl in *. eapply cps_If_True; [exact CVAL | exact STEP].
    + simpl in *. eapply cps_Seq. eapply cps_If_True; [exact CVAL | exact STEP].
  - subst k. destruct k2 as [ | s2'].
    + simpl in *. eapply cps_If_False; [exact CVAL | exact STEP].
    + simpl in *. eapply cps_Seq. eapply cps_If_False; [exact CVAL | exact STEP].
  - subst k. destruct k2 as [ | s2'].
    + simpl in *. eapply cps_While_True; [exact CVAL | exact STEP].
    + simpl in *. eapply cps_Seq. eapply cps_While_True; [exact CVAL | exact STEP].
  - subst k. destruct k2 as [ | s2'].
    + simpl in *. eapply cps_While_False; [exact CVAL | exact STEP].
    + simpl in *. eapply cps_Seq. eapply cps_While_False; [exact CVAL | exact STEP].
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. exact (cps_cont_to_seq_gen (k2 @ k3) k1 c1 c2 STEP k2 k3 Logic.eq_refl). Qed.

Lemma Kapp_empty_r (k : cont) : k @ KEmpty = k.
Proof. destruct k; reflexivity. Qed.

Lemma bs_int_to_cps_int_cont_gen (s : stmt) (c1 c2 : conf) (EXEC : c1 == s ==> c2) :
  forall k c3, KEmpty |- c2 -- k --> c3 -> k |- c1 -- !s --> c3.
Proof.
  induction EXEC as
    [ c
    | s i o x e z VAL
    | s i o x z
    | s i o e z VAL
    | c c' c'' s1 s2 STEP1 IH1 STEP2 IH2
    | s i o c' e s1 s2 CVAL STEP IH
    | s i o c' e s1 s2 CVAL STEP IH
    | st i o c' c'' e s CVAL STEP IH WSTEP WIH
    | st i o e s CVAL
    ]; intros k c3 CSTEP.
  - eapply cps_Skip. exact CSTEP.
  - eapply cps_Assign; [exact VAL | exact CSTEP].
  - eapply cps_Read. exact CSTEP.
  - eapply cps_Write; [exact VAL | exact CSTEP].
  - assert (H2' : (k @ KEmpty) |- c' -- !s2 --> c3)
      by (rewrite Kapp_empty_r; exact (IH2 k c3 CSTEP)).
    apply cps_cont_to_seq in H2'.
    apply IH1 in H2'.
    eapply cps_Seq. exact H2'.
  - eapply cps_If_True; [exact CVAL | exact (IH k c3 CSTEP)].
  - eapply cps_If_False; [exact CVAL | exact (IH k c3 CSTEP)].
  - assert (Hk' : (k @ KEmpty) |- c' -- !(WHILE e DO s END) --> c3)
      by (rewrite Kapp_empty_r; exact (WIH k c3 CSTEP)).
    apply cps_cont_to_seq in Hk'.
    apply IH in Hk'.
    eapply cps_While_True; [exact CVAL | exact Hk'].
  - eapply cps_While_False; [exact CVAL | exact CSTEP].
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  inversion STEP; subst.
  exact (bs_int_to_cps_int_cont_gen s c1 c2 EXEC k c3 CSTEP).
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  exact (bs_int_to_cps_int_cont_gen s (st, i, o) c' EXEC KEmpty c' (cps_Empty c')).
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
