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
Proof. exact (H Hole). Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. remember (Id 0 ::= Nat Z.zero). remember (Id 0 ::= Nat Z.one).
  exists s, s0. split.
    intro. intro. split; intro.
      inversion H. subst. inversion H0. exists [(Id 0, Z.one)]. apply bs_Assign. apply bs_Nat.
      inversion H. subst. inversion H0. exists [(Id 0, Z.zero)]. apply bs_Assign. apply bs_Nat.
    intro. remember (SeqL Hole (COND Var (Id 0) THEN WRITE (Nat Z.one) ELSE WRITE (Nat Z.zero) END)). specialize (H c ([]) ([Z.one])). destruct H. clear H.
      assert (<| c <~ s0 |> [] => [Z.one]). subst. simpl. exists [(Id 0, Z.one)]. apply bs_Seq with ([(Id 0, Z.one)], [], []). apply bs_Assign. apply bs_Nat. apply bs_If_True. apply bs_Var. apply st_binds_hd. apply bs_Write. apply bs_Nat.
      specialize (H0 H). subst. clear H.
        inversion_clear H0. inversion_clear H. inversion STEP1. inversion VAL. subst. clear VAL STEP1.
        inversion_clear STEP2.
          inversion CVAL. inversion VAR. contradiction.
          inversion STEP. inversion VAL.
Qed.

(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Lemma bs_equiv_symm (s1 s2 : stmt) (EQ : s1 ~~~ s2) : s2 ~~~ s1.
Proof. intro. intro. split. apply EQ. apply EQ. Qed.

Lemma bs_equiv_trans (s1 s2 s3 : stmt) (EQ1 : s1 ~~~ s2) (EQ2 : s2 ~~~ s3) : s1 ~~~ s3.
Proof. intro. intro. split; intro. apply EQ2. apply EQ1. exact H. apply EQ1. apply EQ2. exact H. Qed.

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
  Proof. intro. intro. split; intro; inversion H; subst.
    inversion STEP1. subst. apply bs_Seq with c'1. exact STEP0. apply bs_Seq with c'0. exact STEP3. exact STEP2.
    inversion STEP2. subst. apply bs_Seq with c'1. apply bs_Seq with c'0. exact STEP1. exact STEP0. exact STEP3.
  Qed.

  Lemma if_folds (e : expr) (s1 s2 s3 : stmt) :
    (COND e THEN s1 ELSE s2 END ;; s3) ~~~ (COND e THEN s1 ;; s3 ELSE s2 ;; s3 END).
  Proof. intro. intro. split; intro; inversion H; subst.
    inversion STEP1; subst.
      apply bs_If_True.  exact CVAL. apply bs_Seq with c'0. exact STEP. exact STEP2.
      apply bs_If_False. exact CVAL. apply bs_Seq with c'0. exact STEP. exact STEP2.
    inversion STEP; subst. apply bs_Seq with c'0. apply bs_If_True. exact CVAL.  exact STEP1. exact STEP2.
    inversion STEP; subst. apply bs_Seq with c'0. apply bs_If_False. exact CVAL. exact STEP1. exact STEP2.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. intro. intro. split; intro; inversion H; subst.
    apply bs_If_True.  exact CVAL. apply bs_Seq with c'0. exact STEP. apply WSTEP.
    apply bs_If_False. exact CVAL. apply bs_Skip.
    inversion STEP. apply bs_While_True with c'0. exact CVAL. exact STEP1. exact STEP2.
    inversion STEP. apply bs_While_False. exact CVAL.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof. remember (WHILE e DO s END). remember (st, i, o). induction EXE; inversion Heqs0.
    subst. apply IHEXE2. reflexivity. reflexivity.
    inversion Heqp. subst. exact CVAL. Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. intro. intro. split.
    intro. destruct c'. destruct p. assert ([|Nat 1|] s => Z.zero). apply while_false with SKIP l0 l c. exact H. inversion H0.
    intro. inversion H. inversion CVAL. inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    assert (forall (s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf), (c1 == WHILE e DO s1 END ==> c2) -> (c1 == WHILE e DO s2 END ==> c2))).
      intros. remember (WHILE e DO s0 END). induction H0; inversion Heqs; subst.
        apply bs_While_True with c'. exact CVAL. apply H. exact H0_. apply IHbs_int2. reflexivity.
        apply bs_While_False. exact CVAL.
    intro. intro. split; apply H. exact EQ. apply bs_equiv_symm. exact EQ.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. intro. destruct c'. destruct p. subst.
    assert ([|Nat 1|] s0 => Z.zero). apply while_false with s l0 l c. exact H.
    inversion H0.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  assert (forall (s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf), (c1 == s ;; s1 ==> c2) -> (c1 == s ;; s2 ==> c2))).
    intros. inversion H0. subst. apply bs_Seq with c'. exact STEP1. apply H. exact STEP2.
  intro. intro. split; apply H. exact EQ. apply bs_equiv_symm. exact EQ.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  assert (forall (s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf), (c1 == s1 ;; s ==> c2) -> (c1 == s2 ;; s ==> c2))).
    intros. inversion H0. subst. apply bs_Seq with c'. apply H. exact STEP1. exact STEP2.
  intro. intro. split; apply H. exact EQ. apply bs_equiv_symm. exact EQ.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  assert (forall (s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf), (c1 == COND e THEN s ELSE s1 END ==> c2) -> (c1 == COND e THEN s ELSE s2 END ==> c2))).
    intros. inversion H0; subst. apply bs_If_True. exact CVAL. exact STEP. apply bs_If_False. exact CVAL. apply H. exact STEP.
  intro. intro. split; apply H. exact EQ. apply bs_equiv_symm. exact EQ.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  assert (forall (s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf), (c1 == COND e THEN s1 ELSE s END ==> c2) -> (c1 == COND e THEN s2 ELSE s END ==> c2))).
    intros. inversion H0; subst. apply bs_If_True. exact CVAL. apply H. exact STEP. apply bs_If_False. exact CVAL. exact STEP.
  intro. intro. split; apply H. exact EQ. apply bs_equiv_symm. exact EQ.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  assert (forall (s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf), (c1 == WHILE e DO s1 END ==> c2) -> (c1 == WHILE e DO s2 END ==> c2))).
    intros. remember (WHILE e DO s0 END). induction H0; inversion Heqs; subst.
      apply bs_While_True with c'. exact CVAL. apply H. exact H0_. apply IHbs_int2. reflexivity.
      apply bs_While_False. exact CVAL.
  intro. intro. split; apply H. exact EQ. apply bs_equiv_symm. exact EQ.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. apply eq_congruence_seq_r. exact EQ.
  split. apply eq_congruence_seq_l. exact EQ.
  split. apply eq_congruence_cond_else. exact EQ.
  split. apply eq_congruence_cond_then. exact EQ.
  apply eq_congruence_while. exact EQ.
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
Proof. generalize dependent c2. induction EXEC1; intros; inversion EXEC2.
  reflexivity.
  assert (z = z0). apply eval_deterministic with e s. exact VAL. exact VAL0. subst. reflexivity.
  reflexivity.
  assert (z = z0). apply eval_deterministic with e s. exact VAL. exact VAL0. subst. reflexivity.
  assert (c' = c'0). apply IHEXEC1_1. exact STEP1. subst. apply IHEXEC1_2. exact STEP2.
  apply IHEXEC1. exact STEP.
  assert (Z.one = Z.zero). apply eval_deterministic with e s. exact CVAL. exact CVAL0. inversion H6.
  assert (Z.one = Z.zero). apply eval_deterministic with e s. exact CVAL0. exact CVAL. inversion H6.
  apply IHEXEC1. exact STEP.
  assert (c' = c'0). apply IHEXEC1_1. exact STEP. subst. apply IHEXEC1_2. exact WSTEP.
  assert (Z.one = Z.zero). apply eval_deterministic with e st. exact CVAL. exact CVAL0. inversion H5.
  assert (Z.one = Z.zero). apply eval_deterministic with e st. exact CVAL0. exact CVAL. inversion H5.
  reflexivity.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma upd_equiv_states
  (s1 s2 : state Z)
  (HE : equivalent_states s1 s2)
  (i : id) (z : Z) :
  equivalent_states (s1 [i <- z]) (s2 [i <- z]).
Proof. intro. intro. split; intro.
  inversion H; subst. apply st_binds_hd. apply st_binds_tl. exact H5. apply (HE id z0). exact H6.
  inversion H; subst. apply st_binds_hd. apply st_binds_tl. exact H5. apply (HE id z0). exact H6.
Qed.

Lemma eval_equiv_states
  (s1 s2 : state Z)
  (HE : equivalent_states s1 s2)
  (e : expr) (z : Z)
  (H : [|e|] s1 => z) : [|e|] s2 => z.
Proof. induction H; intros.
  apply bs_Nat.
  apply bs_Var. apply HE. exact VAR.
  apply bs_Add. exact (IHeval1 HE). exact (IHeval2 HE).
  apply bs_Sub. exact (IHeval1 HE). exact (IHeval2 HE).
  apply bs_Mul. exact (IHeval1 HE). exact (IHeval2 HE).
  apply bs_Div. exact (IHeval1 HE). exact (IHeval2 HE). exact NZERO.
  apply bs_Mod. exact (IHeval1 HE). exact (IHeval2 HE). exact NZERO.
  apply bs_Le_T with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Le_F with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Lt_T with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Lt_F with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Ge_T with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Ge_F with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Gt_T with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Gt_F with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Eq_T with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Eq_F with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Ne_T with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_Ne_F with za zb. exact (IHeval1 HE). exact (IHeval2 HE). exact OP.
  apply bs_And. exact (IHeval1 HE). exact (IHeval2 HE). exact BOOLA. exact BOOLB.
  apply bs_Or. exact (IHeval1 HE). exact (IHeval2 HE). exact BOOLA. exact BOOLB.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof. remember (st1, i, o). remember (st2, i', o'). generalize i o i' o' st1 st2 st1' HE1 Heqp Heqp0. clear Heqp0 Heqp HE1 st1' st2 st1 o' i' o i. induction H; intros.
  subst. inversion Heqp0. subst. exists st1'. split. exact HE1. apply bs_Skip.
  inversion Heqp. inversion Heqp0. subst. exists (st1' [x <- z]). split. apply upd_equiv_states. exact HE1. apply bs_Assign. apply eval_equiv_states with st1. exact HE1. exact VAL.
  inversion Heqp. inversion Heqp0. subst. exists (st1' [x <- z]). split. apply upd_equiv_states. exact HE1. apply bs_Read.
  inversion Heqp. inversion Heqp0. subst. exists st1'. split. exact HE1. apply bs_Write. apply eval_equiv_states with st2. exact HE1. exact VAL.
  inversion Heqp. inversion Heqp0. subst. destruct c'. destruct p. assert ((s, l0, l) = (s, l0, l)). reflexivity. destruct (IHbs_int1 i o l0 l st1 s st1' HE1 H1 H3). destruct H4. destruct (IHbs_int2 l0 l i' o' s st2 x H4 H3 H2). destruct H6. exists x0. split. exact H6. apply bs_Seq with (x, l0, l). exact H5. exact H7.
  inversion Heqp. inversion Heqp0. subst. destruct (IHbs_int i0 o0 i' o' st1 st2 st1' HE1 Heqp H0). destruct H1. exists x. split. exact H1. apply bs_If_True. apply eval_equiv_states with st1. exact HE1. exact CVAL. exact H2.
  inversion Heqp. inversion Heqp0. subst. destruct (IHbs_int i0 o0 i' o' st1 st2 st1' HE1 Heqp H0). destruct H1. exists x. split. exact H1. apply bs_If_False. apply eval_equiv_states with st1. exact HE1. exact CVAL. exact H2.
  inversion Heqp. inversion Heqp0. subst. destruct c'. destruct p. assert ((s0, l0, l) = (s0, l0, l)). reflexivity. destruct (IHbs_int1 i0 o0 l0 l st1 s0 st1' HE1 Heqp H2). destruct H3. destruct (IHbs_int2 l0 l i' o' s0 st2 x H3 H2 H1). destruct H5. exists x0. split. exact H5. apply bs_While_True with (x, l0, l). apply eval_equiv_states with st1. exact HE1. exact CVAL. exact H4. exact H6.
  inversion Heqp. inversion Heqp0. subst. exists st1'. split. exact HE1. apply bs_While_False. apply eval_equiv_states with st2. exact HE1. exact CVAL.
Qed.
  
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
    reflexivity.
    assert (z = z0). apply eval_deterministic with e s. exact SVAL. exact SVAL0. subst. reflexivity.
    reflexivity.
    assert (z = z0). apply eval_deterministic with e s. exact SVAL. exact SVAL0. subst. reflexivity.
    assert ((None : (option stmt), c') = (None, c'0)). apply IHEXEC1. exact SSTEP. inversion H. subst. reflexivity.
    assert ((None, c') = (Some s1', c'0)). apply IHEXEC1. exact SSTEP. inversion H.
    assert ((Some s1', c') = (None, c'0)). apply IHEXEC1. exact SSTEP. inversion H.
    assert ((Some s1', c') = (Some s1'0, c'0)). apply IHEXEC1. exact SSTEP. inversion H. subst. reflexivity.
    reflexivity.
    assert (Z.zero = Z.one). apply eval_deterministic with e s. exact SCVAL0. exact SCVAL. inversion H6.
    assert (Z.zero = Z.one). apply eval_deterministic with e s. exact SCVAL. exact SCVAL0. inversion H6.
    reflexivity.
    reflexivity.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof. generalize dependent c''. induction STEP1; intros; inversion STEP2.
    assert ((None : option stmt, c') = (None, c'')). apply ss_int_step_deterministic with s c. exact H. exact H0. inversion H4. reflexivity.
    assert ((None, c') = (Some s', c'0)). apply ss_int_step_deterministic with s c. exact H. exact H0. inversion H5.
    assert ((Some s', c') = (None, c''0)). apply ss_int_step_deterministic with s c. exact H. exact H0. inversion H4.
    assert ((Some s', c') = (Some s'0, c'0)). apply ss_int_step_deterministic with s c. exact H. exact H0. inversion H5. subst. apply IHSTEP1. exact H1.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. induction s; intros; inversion STEP; subst.
    apply bs_Skip.
    apply bs_Assign. exact SVAL.
    apply bs_Read.
    apply bs_Write. exact SVAL.
  Qed.
  (* альтернативное доказательство *)
  (*Proof. remember ((None : option stmt, c')). induction STEP; inversion Heqp.
    apply bs_Skip.
    apply bs_Assign. exact SVAL.
    apply bs_Read.
    apply bs_Write. exact SVAL.
  Qed.*)

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof. generalize dependent c'. induction STEP1; intros.
    apply ss_int_Step with s2 c'. apply ss_Seq_Compl. exact H. exact STEP2.
    apply ss_int_Step with (s' ;; s2) c'. apply ss_Seq_InCompl. exact H. apply IHSTEP1. exact STEP2.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof. generalize dependent s'. generalize c c' c''. induction s; intros; inversion STEP; subst.
    apply bs_Seq with c'0. apply ss_bs_base. exact SSTEP. exact EXEC.
    inversion EXEC; subst. apply bs_Seq with c'1. apply IHs1 with c'0 s1'. exact SSTEP. exact STEP1. exact STEP2.
    apply bs_If_True. exact SCVAL. exact EXEC.
    apply bs_If_False. exact SCVAL. exact EXEC.
    inversion EXEC; subst. inversion STEP0. subst. apply bs_While_True with c'0. exact CVAL. exact STEP1. exact STEP2.
    inversion STEP0; subst. apply bs_While_False. exact CVAL.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. split; intro.
    induction H.
      apply ss_int_Base. apply ss_Skip.
      apply ss_int_Base. apply ss_Assign. exact VAL.
      apply ss_int_Base. apply ss_Read.
      apply ss_int_Base. apply ss_Write. exact VAL.
      apply ss_ss_composition with c'. exact IHbs_int1. exact IHbs_int2.
      apply ss_int_Step with s1 (s, i, o). apply ss_If_True.  exact CVAL. exact IHbs_int.
      apply ss_int_Step with s2 (s, i, o). apply ss_If_False. exact CVAL. exact IHbs_int.
      apply ss_int_Step with (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (st, i, o). apply ss_While.
        apply ss_int_Step with (s ;; WHILE e DO s END) (st, i, o). apply ss_If_True. exact CVAL.
          apply ss_ss_composition with c'. exact IHbs_int1. exact IHbs_int2.
      apply ss_int_Step with (COND e THEN s ;; WHILE e DO s END ELSE SKIP END) (st, i, o). apply ss_While.
        apply ss_int_Step with SKIP (st, i, o). apply ss_If_False. exact CVAL.
          apply ss_int_Base. apply ss_Skip.
    induction H.
      apply ss_bs_base. exact H.
      apply ss_bs_step with c' s'. exact H. exact IHss_int.
  Qed.
  
End SmallStep.

Module Renaming.

  Definition renaming := Renaming.renaming.

  Definition rename_id := Renaming.rename_id.

  Definition renamings_inv := Renaming.renamings_inv.

  Definition renaming_inv := Renaming.renaming_inv.

  Definition renaming_inv2 := Renaming.renaming_inv2.

  Definition rename_expr := Renaming.rename_expr.

  Definition re_rename_expr := Renaming.re_rename_expr.

  Definition rename_state := Renaming.rename_state.

  Definition re_rename_state := Renaming.re_rename_state.

  Definition rename_conf (r : renaming) (c : conf) : conf :=
    match c with
    | (st, i, o) => (rename_state r st, i, o)
    end.

  Lemma re_rename_conf (r r' : renaming) (Hinv : renamings_inv r r') (c : conf) : rename_conf r (rename_conf r' c) = c.
  Proof. destruct c, p. simpl. assert (rename_state r (rename_state r' s) = s). apply re_rename_state. exact Hinv. rewrite -> H. reflexivity. Qed.

  Fixpoint rename (r : renaming) (s : stmt) : stmt :=
    match s with
    | SKIP                       => SKIP
    | x ::= e                    => (rename_id r x) ::= rename_expr r e
    | READ x                     => READ (rename_id r x)
    | WRITE e                    => WRITE (rename_expr r e)
    | s1 ;; s2                   => (rename r s1) ;; (rename r s2)
    | COND e THEN s1 ELSE s2 END => COND (rename_expr r e) THEN (rename r s1) ELSE (rename r s2) END
    | WHILE e DO s END           => WHILE (rename_expr r e) DO (rename r s) END             
    end.

  Lemma re_rename
    (r r' : renaming)
    (Hinv : renamings_inv r r')
    (s    : stmt) : rename r (rename r' s) = s.
  Proof. induction s; simpl.
    reflexivity.
      assert (rename_id r (rename_id r' i) = i). apply Hinv.
      assert (rename_expr r (rename_expr r' e) = e). apply re_rename_expr. exact Hinv.
    rewrite -> H. rewrite -> H0. reflexivity.
      assert (rename_id r (rename_id r' i) = i). apply Hinv.
    rewrite -> H. reflexivity.
      assert (rename_expr r (rename_expr r' e) = e). apply re_rename_expr. exact Hinv.
    rewrite -> H. reflexivity.
    rewrite -> IHs1. rewrite -> IHs2. reflexivity.
      assert (rename_expr r (rename_expr r' e) = e). apply re_rename_expr. exact Hinv.
    rewrite -> H. rewrite -> IHs1. rewrite -> IHs2. reflexivity.
      assert (rename_expr r (rename_expr r' e) = e). apply re_rename_expr. exact Hinv.
    rewrite -> H. rewrite -> IHs. reflexivity.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    rename_state r (st [ x <- z ]) = (rename_state r st) [(rename_id r x) <- z].
  Proof. destruct r. reflexivity. Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof. destruct r. induction Hbs.
    apply bs_Skip.
    apply bs_Assign. apply Renaming.eval_renaming_invariance. exact VAL.
    apply bs_Read.
    apply bs_Write. apply Renaming.eval_renaming_invariance. exact VAL.
    apply bs_Seq with (rename_conf (exist _ x b) c'). exact IHHbs1. exact IHHbs2.
    apply bs_If_True. apply Renaming.eval_renaming_invariance. exact CVAL. exact IHHbs.
    apply bs_If_False. apply Renaming.eval_renaming_invariance. exact CVAL. exact IHHbs.
    apply bs_While_True with (rename_conf (exist _ x b) c'). apply Renaming.eval_renaming_invariance. exact CVAL. exact IHHbs1. exact IHHbs2.
    apply bs_While_False. apply Renaming.eval_renaming_invariance. exact CVAL.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof. destruct (renaming_inv r).
      assert ((rename_conf x (rename_conf r c)) == rename x (rename r s) ==> (rename_conf x (rename_conf r c')) = c == s ==> c').
          assert (rename_conf x (rename_conf r c) = c). apply re_rename_conf. exact H.
          assert (rename x (rename r s) = s). apply re_rename. exact H.
          assert (rename_conf x (rename_conf r c') = c'). apply re_rename_conf. exact H.
        rewrite -> H0. rewrite -> H1. rewrite -> H2. reflexivity.
    rewrite <- H0. apply renaming_invariant_bs. exact Hbs.
  Qed.

  Lemma id_renamed_exists (i : id) (r : renaming) : exists i', rename_id r i' = i.
  Proof. destruct (renaming_inv2 r). exists (rename_id x i). apply H. Qed.

  Lemma state_renamed_exists (s : state Z) (r : renaming) : exists s', rename_state r s' = s.
  Proof. destruct (renaming_inv2 r). induction s.
    exists []. reflexivity.
    destruct IHs. destruct a. destruct (id_renamed_exists i r). exists ((x1, z) :: x0).
        assert (rename_state r ((x1, z) :: x0) = (rename_id r x1, z) :: rename_state r x0). destruct r. reflexivity.
      rewrite -> H2. rewrite -> H1. rewrite -> H0. reflexivity.
  Qed.

  Lemma conf_renamed_exists (c : conf) (r : renaming) : exists c', rename_conf r c' = c.
  Proof. destruct c, p, (state_renamed_exists s r). exists (x, l0, l). simpl. rewrite -> H. reflexivity. Qed.

  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof. intro. intro. split; intro.
    inversion H. exists (rename_state r x).
        assert (rename_conf r ([], i, []) = ([], i, [])). reflexivity.
        assert (rename_conf r (x, [], o) = (rename_state r x, [], o)). reflexivity.
      rewrite <- H1. rewrite <- H2. apply renaming_invariant_bs. exact H0.
    inversion H. destruct (renaming_inv2 r). destruct (conf_renamed_exists (x, [], o) r).
      destruct x1, p. inversion H2. rewrite -> H5 in H2. rewrite -> H6 in H2.
        assert (rename_conf r ([], i, []) = ([], i, [])). reflexivity.
      exists s0. apply renaming_invariant_bs_inv with r. rewrite -> H3. rewrite -> H2. exact H0.
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
Proof. generalize dependent S. induction EXEC; intros.
  inversion DEF.
  destruct k; inversion DEF.
    inversion EXEC. apply bs_Skip.
    apply bs_Seq with c. apply bs_Skip. apply IHEXEC. reflexivity.
  destruct k; inversion DEF.
    inversion EXEC. apply bs_Assign. exact CVAL.
    apply bs_Seq with (s [x <- n], i, o). apply bs_Assign. exact CVAL. apply IHEXEC. reflexivity.
  destruct k; inversion DEF.
    inversion EXEC. apply bs_Read.
    apply bs_Seq with (s [x <- z], i, o). apply bs_Read. apply IHEXEC. reflexivity.
  destruct k; inversion DEF.
    inversion EXEC. apply bs_Write. exact CVAL.
    apply bs_Seq with (s, i, z :: o). apply bs_Write. exact CVAL. apply IHEXEC. reflexivity.
  destruct k; inversion DEF.
    apply IHEXEC. reflexivity.
    apply SmokeTest.seq_assoc. apply IHEXEC. reflexivity.
  destruct k; inversion DEF.
    apply bs_If_True. exact CVAL. apply IHEXEC. reflexivity.
    apply SmokeTest.if_folds. apply bs_If_True. exact CVAL. apply IHEXEC. reflexivity.
  destruct k; inversion DEF.
    apply bs_If_False. exact CVAL. apply IHEXEC. reflexivity.
    apply SmokeTest.if_folds. apply bs_If_False. exact CVAL. apply IHEXEC. reflexivity.
  destruct k; inversion DEF.
    apply SmokeTest.while_unfolds. apply bs_If_True. exact CVAL. apply IHEXEC. reflexivity.
      assert (((st, i, o) == s ;; WHILE e DO s END ;; s0 ==> c') -> ((st, i, o) == WHILE e DO s END ;; s0 ==> c')).
        intro. inversion H. inversion STEP2. subst. apply bs_Seq with c'1. apply bs_While_True with c'0. exact CVAL. exact STEP1. exact STEP0. exact STEP3.
    apply H. apply IHEXEC. reflexivity.
  destruct k; inversion DEF.
    inversion EXEC. apply bs_While_False. exact CVAL.
    apply bs_Seq with (st, i, o). apply bs_While_False. exact CVAL. apply IHEXEC. reflexivity.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. apply cps_bs_gen with (!s1) (!s2). exact STEP. reflexivity. Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. apply cps_bs_gen with (!s) KEmpty. exact STEP. reflexivity. Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. destruct k1; destruct k2; destruct k3.
  inversion STEP. apply cps_Empty.
  inversion STEP.
  inversion STEP.
  inversion STEP.
  exact STEP.
  exact STEP.
  apply cps_Seq. exact STEP.
  apply cps_Seq. exact STEP.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. inversion_clear STEP. subst. generalize dependent k. generalize c3. induction EXEC; intros.
  apply cps_Skip. exact CSTEP.
  apply cps_Assign with z. exact VAL. exact CSTEP.
  apply cps_Read. exact CSTEP.
  apply cps_Write with z. exact VAL. exact CSTEP.
  apply cps_Seq. apply IHEXEC1. destruct k. apply IHEXEC2. exact CSTEP. apply cps_Seq. apply IHEXEC2. exact CSTEP.
  apply cps_If_True. exact CVAL. apply IHEXEC. exact CSTEP.
  apply cps_If_False. exact CVAL. apply IHEXEC. exact CSTEP.
  apply cps_While_True. exact CVAL. apply IHEXEC1. destruct k. apply IHEXEC2. exact CSTEP. apply cps_Seq. apply IHEXEC2. exact CSTEP.
  apply cps_While_False. exact CVAL. exact CSTEP.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. apply bs_int_to_cps_int_cont with c'. exact EXEC. apply cps_Skip. apply cps_Empty. Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
