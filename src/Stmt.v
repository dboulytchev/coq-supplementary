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
Proof. apply (H Hole). Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. pose (Id 1 ::= Nat 1). pose (Id 1, Z.one). exists s, SKIP. split.
- intros i o. split; intro; destruct H.
  + inversion H. subst. inversion VAL. subst.
    exists []. apply bs_Skip.
  + inversion H. subst.
    exists [p]. apply bs_Assign. apply bs_Nat.
- intro. pose (SeqL Hole (WRITE (Var (Id 1)))). pose (H c ([]) ([Z.one])). inversion i.
  assert (eval (c <~ s) ([]) ([Z.one])).
  + simpl. exists [p]. apply (bs_Seq ([], [], []) ([p], [], [])).
   * apply bs_Assign. apply bs_Nat.
   * apply bs_Write. apply bs_Var. apply st_binds_hd.
  + apply H0 in H2. inversion H2. inversion H3. subst.
    inversion STEP1. subst. inversion STEP2. subst.
    inversion VAL. subst. inversion VAR.
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
  Proof. intros c c'. split; intro H; seq_inversion; seq_inversion; seq_apply. Qed.

  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. intros c c'. split.
  - intro. inversion H; subst.
    + apply bs_If_True.
      * assumption.
      * apply (bs_Seq (st, i, o) c'0 c'); assumption.
    + apply bs_If_False.
      * assumption.
      * apply bs_Skip.
  - intro. inversion H; subst.
    + inversion STEP. subst. apply (bs_While_True s0 i o c'0 c'); assumption.
    + inversion STEP; subst. apply bs_While_False. assumption.
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof. remember (WHILE e DO s END). remember (st, i, o).
    induction EXE; inversion Heqs0; subst.
    - apply IHEXE2 in Heqs0.
      + assumption.
      + reflexivity.
    - inversion Heqp. subst. assumption.
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. intros c c'. split.
  - intro. remember (WHILE (Nat 1) DO SKIP END). induction H; inversion Heqs; subst.
    + inversion H; subst. apply IHbs_int2 in Heqs. assumption.
    + inversion CVAL.
  - intro. inversion H; subst; inversion CVAL.
  Qed.

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof. intros c c'. split.
  - intro. remember (WHILE e DO s1 END). induction H; inversion Heqs; subst.
    + apply (bs_While_True st i o c' c'').
      * assumption.
      * apply EQ. assumption.
      * apply IHbs_int2 in Heqs. assumption.
    + apply bs_While_False. assumption.
  - intro. remember (WHILE e DO s2 END). induction H; inversion Heqs; subst.
    + apply (bs_While_True st i o c' c'').
      * assumption.
      * apply EQ. assumption.
      * apply IHbs_int2 in Heqs. assumption.
    + apply bs_While_False. assumption.
  Qed.

  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. intro. remember (WHILE (Nat 1) DO s END). induction H; inversion Heqs0; subst.
  - apply IHbs_int2 in Heqs0. assumption.
  - inversion CVAL.
  Qed.

End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof. intros c c'. split.
- intro. seq_inversion. apply (bs_Seq c c'0 c').
  + assumption.
  + apply EQ. assumption.
- intro. seq_inversion. apply (bs_Seq c c'0 c').
  + assumption.
  + apply EQ. assumption.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof. intros c c'. split.
- intro. seq_inversion. apply (bs_Seq c c'0 c').
  + assumption
  + apply EQ. assumption.
  + assumption.
- intro. seq_inversion. apply (bs_Seq c c'0 c').
  + assumption
  + apply EQ. assumption.
  + assumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. intros c c'. split.
- intro. inversion H; subst.
  + apply bs_If_True; assumption.
  + apply bs_If_False.
    * assumption.
    * apply EQ. assumption.
- intro. inversion H; subst.
  + apply bs_If_True; assumption.
  + apply bs_If_False.
    * assumption.
    * apply EQ. assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. intros c c'. split.
- intro. inversion H; subst.
  + apply bs_If_True.
    * assumption.
    * apply EQ. assumption.
  + apply bs_If_False; assumption.
- intro. inversion H; subst.
  + apply bs_If_True.
    * assumption.
    * apply EQ. assumption.
  + apply bs_If_False; assumption.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. apply SmokeTest.while_eq. assumption. Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. apply eq_congruence_seq_r.     assumption.
  split. apply eq_congruence_seq_l.     assumption.
  split. apply eq_congruence_cond_else. assumption.
  split. apply eq_congruence_cond_then. assumption.
         apply eq_congruence_while.     assumption.
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
Proof. generalize dependent c2. induction EXEC1; intros; inversion EXEC2; subst.
- reflexivity.
- by_eval_deterministic.
- reflexivity.
- by_eval_deterministic.
- apply IHEXEC1_1 in STEP1. subst. apply IHEXEC1_2 in STEP2. subst. reflexivity.
- apply IHEXEC1. assumption.
- eval_zero_not_one.
- eval_zero_not_one.
- apply IHEXEC1. assumption.
- apply IHEXEC1_1 in STEP. subst.  apply IHEXEC1_2. assumption.
- eval_zero_not_one.
- eval_zero_not_one.
- reflexivity.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma equivalent_states_eval (e : expr) (s1 s2 : state Z) (z : Z)
  (HE : equivalent_states s1 s2)
  (H  : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof. induction H; econstructor; eauto. apply HE. assumption. Qed.

Lemma equivalent_states_update (st1 st2 : state Z) (x : id) (z : Z)
  (HE : equivalent_states st1 st2) :
  equivalent_states (st1 [x <- z]) (st2 [x <- z]).
Proof. intro id. destruct (id_eq_dec x id); subst; intro z0; split; intro H; inversion H; subst.
- apply st_binds_hd.
- apply st_binds_tl.
  + assumption.
  + apply HE. assumption.
- apply st_binds_hd.
- apply st_binds_tl.
  + assumption.
  + apply HE. assumption.
- apply st_binds_hd.
- apply st_binds_tl.
  + assumption.
  + apply HE. assumption.
- apply st_binds_hd.
- apply st_binds_tl.
  + assumption.
  + apply HE. assumption.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof. revert st1' HE1 . remember (st1, i, o). remember (st2, i', o').
  revert st1 i o Heqp. revert st2 i' o' Heqp0.
  induction H; intros; inversion Heqp; inversion Heqp0; subst.
- exists st1'. split
  + intro. inversion H. subst. assumption.
  + inversion H. subst. apply bs_Skip.
- exists (st1' [x <- z]). split.
  + apply equivalent_states_update. assumption.
  + apply bs_Assign. apply (equivalent_states_eval e st1 st1'); assumption.
- exists (st1' [x <- z]). split.
  + apply equivalent_states_update. assumption.
  + apply bs_Read.
- exists st1'. split.
  + assumption.
  + apply bs_Write. apply (equivalent_states_eval e st2 st1'); assumption.
- destruct c' as [[st3 i3] o3].
  destruct (IHbs_int1 st3 i3 o3 Coq.Init.Logic.eq_refl st1 i o Coq.Init.Logic.eq_refl st1').
  + assumption.
  + destruct (IHbs_int2 st2 i' o' Coq.Init.Logic.eq_refl st3 i3 o3 Coq.Init.Logic.eq_refl x).
    * inversion H3. assumption.
    * exists x0. split. inversion H4.
      assumption.
      apply (bs_Seq (st1', i, o) (x, i3, o3) (x0, i', o')).
        inversion H3. assumption.
        inversion H4. assumption.
- destruct (IHbs_int st2 i' o' Coq.Init.Logic.eq_refl st1 i0 o0 Coq.Init.Logic.eq_refl st1').
  + assumption.
  + exists x. split.
    * inversion H1. assumption.
    * apply bs_If_True.
      apply (equivalent_states_eval e st1 st1'); assumption.
      inversion H1. assumption.
- destruct (IHbs_int st2 i' o' Coq.Init.Logic.eq_refl st1 i0 o0 Coq.Init.Logic.eq_refl st1').
  + assumption.
  + exists x. split.
    * inversion H1. assumption.
    * apply bs_If_False.
      apply (equivalent_states_eval e st1 st1'); assumption.
      inversion H1. assumption.
- destruct c' as [[st3 i3] o3].
  destruct (IHbs_int1 st3 i3 o3 Coq.Init.Logic.eq_refl st1 i0 o0 Coq.Init.Logic.eq_refl st1').
  + assumption.
  + destruct (IHbs_int2 st2 i' o' Coq.Init.Logic.eq_refl st3 i3 o3 Coq.Init.Logic.eq_refl x).
    * inversion H2. assumption.
    * exists x0. split. inversion H3.
      assumption.
      apply (bs_While_True st1' i0 o0 (x, i3, o3) (x0, i', o')).
        inversion H3.  apply (equivalent_states_eval e st1 st1'); assumption.
        inversion H2. assumption.
        inversion H3. assumption.
- inversion Heqp. inversion Heqp0. subst. exists st1'. split.
  + assumption.
  + apply bs_While_False. apply (equivalent_states_eval e st2 st1'); assumption.
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
  Proof. generalize dependent c''. induction EXEC1; intros; inversion EXEC2; subst.
  - reflexivity.
  - by_eval_deterministic.
  - reflexivity.
  - by_eval_deterministic.
  - apply IHEXEC1 in SSTEP. inversion SSTEP. reflexivity.
  - apply IHEXEC1 in SSTEP. inversion SSTEP.
  - apply IHEXEC1 in SSTEP. inversion SSTEP.
  - apply IHEXEC1 in SSTEP. inversion SSTEP. reflexivity.
  - reflexivity.
  - eval_zero_not_one.
  - eval_zero_not_one.
  - reflexivity.
  - reflexivity.
  Qed.

  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof. generalize dependent c''. induction STEP1; intros; inversion STEP2; subst.
  - apply (ss_int_step_deterministic s c (None, c') (None, c'')) in H0.
    + inversion H0. reflexivity.
    + assumption.
  - apply (ss_int_step_deterministic s c (None, c') (Some s', c'0)) in H0.
    + inversion H0.
    + assumption.
  - apply (ss_int_step_deterministic s c (Some s', c') (None, c''0)) in H0.
    + inversion H0.
    + assumption.
  - apply (ss_int_step_deterministic s c (Some s', c') (Some s'0, c'0)) in H0.
    + inversion H1; subst; apply IHSTEP1; inversion H0; subst; assumption.
    + assumption.
  Qed.

  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. inversion STEP; subst.
  - apply bs_Skip.
  - apply bs_Assign. assumption.
  - apply bs_Read.
  - apply bs_Write. assumption.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'.
  Proof. induction STEP1.
  - apply (ss_int_Step (s ;; s2) s2 c c'0 c').
    + apply ss_Seq_Compl. assumption.
    + assumption.
  - apply (ss_int_Step (s ;; s2) (s' ;; s2) c c'0 c').
    + apply ss_Seq_InCompl. assumption.
    + apply IHSTEP1. assumption.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof. generalize dependent c''. remember (Some s', c'). generalize dependent s'.
    induction STEP; intros; inversion Heqp; subst.
    - apply (bs_Seq c c' c'').
      + apply ss_bs_base. assumption.
      + assumption.
    - inversion EXEC; subst. apply (bs_Seq c c'0 c'').
      + apply (IHSTEP s1').
        * reflexivity.
        * assumption.
      + assumption.
    - apply bs_If_True; assumption.
    - apply bs_If_False; assumption.
    - apply SmokeTest.while_unfolds. assumption.
  Qed.

  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. split; intro H; induction H.
  - apply ss_int_Base. apply ss_Skip.
  - apply ss_int_Base. apply ss_Assign. assumption.
  - apply ss_int_Base. apply ss_Read.
  - apply ss_int_Base. apply ss_Write. assumption.
  - apply (ss_ss_composition c c'' c' s1 s2); assumption.
  - apply (ss_int_Step (COND e THEN s1 ELSE s2 END) s1 (s, i, o) (s, i, o)).
    + apply ss_If_True. assumption.
    + assumption.
  - apply (ss_int_Step (COND e THEN s1 ELSE s2 END) s2 (s, i, o) (s, i, o)).
    + apply ss_If_False. assumption.
    + assumption.
  - apply (ss_int_Step (WHILE e DO s END) (COND e THEN s;;WHILE e DO s END ELSE SKIP END) (st, i, o) (st, i, o)).
    + apply ss_While.
    + apply (ss_int_Step (COND e THEN s;;WHILE e DO s END ELSE SKIP END) (s;;WHILE e DO s END) (st, i, o) (st, i, o)).
      * apply ss_If_True. assumption.
      * apply (ss_ss_composition (st,i,o) c'' c' s (WHILE e DO s END)); assumption.
  - apply (ss_int_Step (WHILE e DO s END) (COND e THEN s;;WHILE e DO s END ELSE SKIP END) (st, i, o) (st, i, o) (st, i, o)).
    + apply ss_While.
    + apply (ss_int_Step (COND e THEN s;;WHILE e DO s END ELSE SKIP END) SKIP (st, i, o) (st, i, o) (st, i, o)).
      * apply ss_If_False. assumption.
      * apply ss_int_Base. apply ss_Skip.
  - apply ss_bs_base. assumption.
  - apply (ss_bs_step c c' c'' s s'); assumption.
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
  Proof. induction s; simpl.
  - reflexivity.
  - rewrite Hinv. rewrite Renaming.re_rename_expr.
    + reflexivity.
    + assumption.
  - rewrite Hinv. reflexivity.
  - rewrite Renaming.re_rename_expr.
    + reflexivity.
    + assumption.
  - rewrite IHs1. rewrite IHs2. reflexivity.
  - rewrite Renaming.re_rename_expr. rewrite IHs1. rewrite IHs2.
    + reflexivity.
    + assumption.
  - rewrite Renaming.re_rename_expr. rewrite IHs.
    + reflexivity.
    + assumption.
  Qed.

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. destruct r. simpl. reflexivity. Qed.

  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof. destruct r. pose (exist (fun f : id -> id => FinFun.Bijective f) x b). induction Hbs; simpl.
  - apply bs_Skip.
  - apply bs_Assign. apply Renaming.eval_renaming_invariance. assumption.
  - apply bs_Read.
  - apply bs_Write. apply Renaming.eval_renaming_invariance. assumption.
  - apply (bs_Seq (rename_conf s0 c) (rename_conf s0 c') (rename_conf s0 c'') (rename s0 s1) (rename s0 s2)).
    + apply IHHbs1.
    + apply IHHbs2.
  - apply bs_If_True.
    + apply Renaming.eval_renaming_invariance. assumption.
    + apply IHHbs.
  - apply bs_If_False.
    + apply Renaming.eval_renaming_invariance. assumption.
    + apply IHHbs.
  - apply (bs_While_True (Renaming.rename_state s0 st) i o (rename_conf s0 c') (rename_conf s0 c'')
           (Renaming.rename_expr s0 e) (rename s0 s)).
    + apply Renaming.eval_renaming_invariance. assumption.
    + apply IHHbs1.
    + apply IHHbs2.
  - apply bs_While_False. apply Renaming.eval_renaming_invariance. assumption.
  Qed.

  Lemma re_rename_conf
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (c    : conf) : rename_conf r (rename_conf r' c) = c.
  Proof. generalize dependent c. intros [[s i] o]. simpl.
    rewrite (Renaming.re_rename_state r r' Hinv). reflexivity.
  Qed.

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof. destruct (Renaming.renaming_inv r).
    apply (renaming_invariant_bs (rename r s) x (rename_conf r c) (rename_conf r c')) in Hbs.
    rewrite re_rename in Hbs.
    - rewrite re_rename_conf in Hbs; rewrite re_rename_conf in Hbs; assumption.
    - assumption.
  Qed.

  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof. intros i o. split; intro; destruct H.
  - apply (renaming_invariant_bs s r) in H. simpl in H.
    exists (Renaming.rename_state r x). assumption.
  - destruct (Renaming.renaming_inv2 r). exists (Renaming.rename_state x0 x).
    apply (renaming_invariant_bs_inv s r). simpl. rewrite (Renaming.re_rename_state); assumption.
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
- inversion DEF.
- cps_bs_gen_helper k DEF bs_Skip.
- cps_bs_gen_helper k DEF bs_Assign.
- cps_bs_gen_helper k DEF bs_Read.
- cps_bs_gen_helper k DEF bs_Write.
- destruct k; inversion DEF; subst.
  + apply IHEXEC. reflexivity.
  + apply SmokeTest.seq_assoc. apply IHEXEC. reflexivity.
- destruct k; inversion DEF. subst.
  + apply bs_If_True.
    * assumption.
    * apply IHEXEC. reflexivity.
  + assert ((s, i, o) == s1 ;; s0 ==> c').
    * apply IHEXEC. reflexivity.
    * inversion H. subst. apply (bs_Seq (s, i, o) c'0). apply bs_If_True; assumption. assumption.
- destruct k; inversion DEF. subst.
  + apply bs_If_False.
    * assumption.
    * apply IHEXEC. reflexivity.
  + assert ((s, i, o) == s2 ;; s0 ==> c').
    * apply IHEXEC. reflexivity.
    * inversion H. subst. apply (bs_Seq (s, i, o) c'0). apply bs_If_False; assumption. assumption.
- destruct k; inversion DEF. subst.
  + assert ((st, i, o) == s ;; WHILE e DO s END ==> c').
    * apply IHEXEC. reflexivity.
    * inversion H. subst. apply (bs_While_True st i o c'0); assumption.
  +  assert ((st, i, o) == s ;; (WHILE e DO s END ;; s0) ==> c').
    * apply IHEXEC. reflexivity.
    * apply SmokeTest.seq_assoc in H. inversion H. subst. inversion STEP1. subst.
      apply (bs_Seq (st, i, o) c'0).
      apply (bs_While_True st i o c'1); assumption. assumption.
- cps_bs_gen_helper k DEF bs_While_False.
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. apply (cps_bs_gen (s1 ;; s2) c c' !s1 !s2).
- assumption.
- reflexivity.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') :
  c == s ==> c'.
Proof. apply (cps_bs_gen s c c' !s KEmpty).
- assumption.
- reflexivity.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. destruct k1.
- destruct k2.
  + destruct k3.
    * inversion STEP. subst. assumption.
    * inversion STEP.
  + destruct k3; inversion STEP.
- destruct k2.
  + apply STEP.
  + apply cps_Seq. apply STEP.
Qed.

Lemma kapp_k_empty k : k @ KEmpty = k.
Proof. destruct k; reflexivity. Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. generalize dependent k. generalize dependent c3. induction EXEC; intros.
- assumption.
- apply cps_Assign with z.
  + assumption.
  + inversion STEP. subst. assumption.
- apply cps_Read. inversion STEP. subst. assumption.
- apply cps_Write with z.
  + assumption.
  + inversion STEP. subst. assumption.
- apply cps_Seq. apply IHEXEC1. apply cps_Skip. apply cps_cont_to_seq. rewrite kapp_k_empty.
  apply IHEXEC2. assumption.
- apply cps_If_True.
  + assumption.
  + apply IHEXEC. assumption.
- apply cps_If_False.
  + assumption.
  + apply IHEXEC. assumption.
- apply cps_While_True.
  + assumption.
  + apply IHEXEC1. apply cps_Skip. apply cps_cont_to_seq. rewrite kapp_k_empty.
    apply IHEXEC2. assumption.
- apply cps_While_False.
  + assumption.
  + inversion STEP. subst. assumption.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. apply (bs_int_to_cps_int_cont (st, i, o) c').
- assumption.
- apply cps_Skip. apply cps_Empty.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
