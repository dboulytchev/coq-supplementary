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
  specialize (H Hole).
  simpl in H.
  assumption.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists (Id 0 ::= Nat 5), (Id 0 ::= Nat 10).
  split.
  - unfold eval_equivalent, eval. intros i o. split; intros [st H_bs];
    inversion H_bs; subst; eexists; repeat constructor.

  - intro H_equiv.
    specialize (H_equiv (SeqL Hole (WRITE (Var (Id 0)))) nil (5%Z :: nil)).
    simpl in H_equiv.
    destruct H_equiv as [H_forward _].
    specialize (H_forward ltac:(unfold eval; eexists; eapply bs_Seq; repeat constructor)).
    
    unfold eval in H_forward.
    destruct H_forward as [st' H_wrong].
    
    inversion H_wrong; subst; clear H_wrong.
    
    repeat match goal with
           | H : _ == _ ==> _ |- _ => inversion H; subst; clear H
           | H : [| _ |] _ => _ |- _ => inversion H; subst; clear H
           | H : _ / _ => _ |- _ => inversion H; subst; clear H
           | H : bs_int _ _ _ |- _ => inversion H; subst; clear H
           end.
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
    intros c c'.
    split; intro H.
    - seq_inversion. 
      seq_inversion. 
      seq_apply.
    - seq_inversion.
      seq_inversion.
      seq_apply.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent; intros c c'; split; intro H.
    - inversion H; subst; [econstructor 6 | econstructor 7]; eauto.
    - inversion H; subst.
      + seq_inversion. econstructor 8; eauto.
      + inversion STEP; subst. econstructor 9; eauto.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as wstmt eqn:Heqw.
    remember (st, i, o) as c' eqn:Heqc'.
    induction EXE; inversion Heqw; subst.
    - apply IHEXE2; reflexivity.
    - inversion Heqc'; subst.
      assumption.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros c c'.
    split; intro H.
    - destruct c' as [[st i] o].
      apply while_false in H.
      inversion H.
    - inversion H; subst;
      inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent in *.
    intros c c'.
    split; intro H.
    - remember (WHILE e DO s1 END) as wstmt eqn:Heqw.
      induction H; inversion Heqw; subst.
      + eapply bs_While_True.
        * eexact CVAL.
        * apply EQ. eexact H.
        * apply IHbs_int2. reflexivity.
      + eapply bs_While_False.
        eexact CVAL.
    - remember (WHILE e DO s2 END) as wstmt eqn:Heqw.
      induction H; inversion Heqw; subst.
      + eapply bs_While_True.
        * eexact CVAL.
        * apply EQ. eexact H.
        * apply IHbs_int2. reflexivity.
      + eapply bs_While_False.
        eexact CVAL.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    intro H.
    remember (WHILE (Nat 1) DO s END) as wstmt eqn:Heqw.
    induction H; inversion Heqw; subst.
    - apply IHbs_int2. reflexivity.
    - inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro H.
  - seq_inversion.
    eapply bs_Seq.
    + eexact STEP1.
    + apply EQ. eexact STEP2.
  - seq_inversion.
    eapply bs_Seq.
    + eexact STEP1.
    + apply EQ. eexact STEP2.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro H.
  - seq_inversion.
    eapply bs_Seq.
    + apply EQ. eexact STEP1.
    + eexact STEP2.
  - seq_inversion.
    eapply bs_Seq.
    + apply EQ. eexact STEP1.
    + eexact STEP2.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro H.
  - inversion H; subst.
    + eapply bs_If_True.
      * eexact CVAL.
      * eexact STEP.
    + eapply bs_If_False.
      * eexact CVAL.
      * apply EQ. eexact STEP.
  - inversion H; subst.
    + eapply bs_If_True.
      * eexact CVAL.
      * eexact STEP.
    + eapply bs_If_False.
      * eexact CVAL.
      * apply EQ. eexact STEP.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent in *.
  intros c c'.
  split; intro H.
  - inversion H; subst.
    + eapply bs_If_True.
      * eexact CVAL.
      * apply EQ. eexact STEP.
    + eapply bs_If_False.
      * eexact CVAL.
      * eexact STEP.
  - inversion H; subst.
    + eapply bs_If_True.
      * eexact CVAL.
      * apply EQ. eexact STEP.
    + eapply bs_If_False.
      * eexact CVAL.
      * eexact STEP.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  unfold bs_equivalent in *; intros c c'; split; intro H.
  - remember (WHILE e DO s1 END) as wstmt eqn:Heqw.
    induction H; inversion Heqw; subst; [econstructor 8 | econstructor 9]; eauto; apply EQ; eauto.
  - remember (WHILE e DO s2 END) as wstmt eqn:Heqw.
    induction H; inversion Heqw; subst; [econstructor 8 | econstructor 9]; eauto; apply EQ; eauto.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. { apply eq_congruence_seq_r. assumption. }
  split. { apply eq_congruence_seq_l. assumption. }
  split. { apply eq_congruence_cond_else. assumption. }
  split. 
  - unfold bs_equivalent in *. intros c c'.
    specialize (eq_congruence_cond_then e s s1 s2 EQ c c').
    firstorder.
  - apply eq_congruence_while. assumption. 
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
  induction EXEC1; intros; inversion EXEC2; subst; intuition;
  try (apply (eval_deterministic e s z z0) in VAL; subst; intuition; fail);
  try eval_zero_not_one.
  - repeat match goal with
    | [ IH : forall c2, _ == _ ==> c2 -> _, H : _ == _ ==> _ |- _ ] => 
        specialize (IH _ H); subst
    end; intuition.
  - repeat match goal with
    | [ IH : forall c2, _ == _ ==> c2 -> _, H : _ == _ ==> _ |- _ ] => 
        specialize (IH _ H); subst
    end; intuition.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.
  
Require Import Stdlib.Program.Equality.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')  
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
  Proof.
    generalize dependent st1'.
    dependent induction H; intros.
    - exists st1'. auto.
    - exists (st1' [x <- z]). split.
      + unfold equivalent_states; intros y v; split; intros Hb;
        destruct (id_eq_dec y x); subst; inversion Hb; subst; constructor; auto; try apply HE1; auto.
      + constructor; eapply variable_relevance; eauto.
    - exists (st1' [x <- z]). split.
      + unfold equivalent_states; intros y v; split; intros Hb;
        destruct (id_eq_dec y x); subst; inversion Hb; subst; constructor; auto; try apply HE1; auto.
      + constructor.
    - exists st1'. 
      split.
      + assumption.
      + constructor. eapply variable_relevance; auto.
    - destruct c' as [[st4 i4] o4].
      specialize (IHbs_int1 i o i4 o4 st1 st4 JMeq_refl JMeq_refl st1' HE1).
      destruct IHbs_int1 as [st4' [HE4 STEP1']].
      specialize (IHbs_int2 i4 o4 i' o' st4 st2 JMeq_refl JMeq_refl st4' HE4).
      destruct IHbs_int2 as [st2' [HE2 STEP2']].
      exists st2'. split.
      + assumption.
      + econstructor; eassumption.
    - edestruct IHbs_int as [st2' [HE2 STEP']]; eauto.
      exists st2'. split; eauto.
      apply bs_If_True.
      + eapply variable_relevance; eauto.
      + assumption.
    - edestruct IHbs_int as [st2' [HE2 STEP']]; eauto.
      exists st2'. split; eauto.
      apply bs_If_False.
      + eapply variable_relevance; eauto.
      + assumption.
    - destruct c' as [[st4 i4] o4].
      specialize (IHbs_int1 i o i4 o4 st1 st4 JMeq_refl JMeq_refl st1' HE1).
      destruct IHbs_int1 as [st4' [HE4 STEP1']].
      specialize (IHbs_int2 i4 o4 i' o' st4 st2 JMeq_refl JMeq_refl st4' HE4).
      destruct IHbs_int2 as [st2' [HE2 STEP2']].
      exists st2'. split.
      + assumption.
      + eapply bs_While_True.
        * eapply variable_relevance; auto.
        * eassumption.
        * assumption.
    - exists st1'. split.
      + assumption.
      + apply bs_While_False. eapply variable_relevance; auto.
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
    induction EXEC1; intros; inversion EXEC2; subst;
    repeat f_equal;
    try congruence;
    try solve [eapply eval_deterministic; eassumption];
    try solve [apply IHEXEC1 in SSTEP; congruence];
    try solve [apply IHEXEC1_1 in SSTEP1; congruence];
    try solve [apply IHEXEC1_2 in SSTEP2; congruence].
    all: try match goal with
    | [ H1 : [| ?e |] ?st => (?v1), H2 : [| ?e |] ?st => (?v2) |- _ ] =>
      assert (v1 = v2) by (eapply eval_deterministic; eassumption); 
      discriminate || congruence
    end.
    all: try match goal with
    | [ IH : context[_ -> _ = _], H : _ -- _ --> _ |- _ ] =>
      apply IH in H; inversion H; subst; clear H
    end.
    all: try assumption; try congruence; auto; eauto.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''. 
    induction STEP1; intros; inversion STEP2; subst; auto.
    all: repeat match goal with
    | [ H1 : ?c -- ?s --> ?c1, H2 : ?c -- ?s --> ?c2 |- _ ] =>
      apply (ss_int_step_deterministic s c c1 c2 H1) in H2;
      inversion H2; subst; clear H2; try reflexivity
    end.
    all: eauto.
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
    induction STEP1; intros.
    all: try (apply IHSTEP1 in STEP2).
    all: eapply ss_int_Step.
    all: try solve [ apply ss_Seq_Compl; assumption | apply ss_Seq_Compl; eauto ].
    all: try solve [ apply ss_Seq_InCompl; eassumption | apply ss_Seq_InCompl; eauto ].
    all: auto; eauto.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof. 
    generalize dependent c''.
    dependent induction s; intros; inversion STEP; subst.
    - eapply bs_Seq; [apply ss_bs_base; eassumption | assumption].
    - inversion EXEC; subst; eapply bs_Seq; [eapply IHs1; eassumption | assumption].
    - apply bs_If_True; assumption.
    - apply bs_If_False; assumption.
    - inversion EXEC; inversion STEP0; subst;
      [eapply bs_While_True | apply bs_While_False]; eassumption || assumption.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. 
    split; intro H.
    - induction H; try solve [ apply ss_int_Base; constructor; assumption 
                            | apply ss_int_Base; constructor ].
      + eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step; [apply ss_If_True; eassumption | assumption].
      + eapply ss_int_Step; [apply ss_If_False; eassumption | assumption].
      + eapply ss_int_Step; [apply ss_While | idtac].
        eapply ss_int_Step; [apply ss_If_True; eassumption | idtac].
        eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step; [apply ss_While | idtac].
        eapply ss_int_Step; [apply ss_If_False; eassumption | idtac].
        apply ss_int_Base, ss_Skip.
    - induction H.
      + apply ss_bs_base; assumption.
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
    induction s; simpl;
    try reflexivity;
    try rewrite Renaming.re_rename_expr; auto;
    try rewrite Hinv; auto;
    try rewrite IHs1, IHs2;
    try rewrite IHs;
    try assumption;
    try reflexivity.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. 
    destruct r. 
    simpl. 
    unfold update. 
    reflexivity. 
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r as [f Hbij].
    induction Hbs; simpl.
    - constructor.
    - constructor; apply -> Renaming.eval_renaming_invariance; assumption.
    - constructor.
    - constructor; apply -> Renaming.eval_renaming_invariance; assumption.
    - eapply bs_Seq; [apply IHHbs1 | apply IHHbs2].
    - apply bs_If_True; [apply -> Renaming.eval_renaming_invariance; assumption | apply IHHbs].
    - apply bs_If_False; [apply -> Renaming.eval_renaming_invariance; assumption | apply IHHbs].
    - eapply bs_While_True; [apply -> Renaming.eval_renaming_invariance; assumption | apply IHHbs1 | apply IHHbs2].
    - apply bs_While_False; apply -> Renaming.eval_renaming_invariance; assumption.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    pose proof (Renaming.renaming_inv r) as [r' Hinv].
    eapply renaming_invariant_bs in Hbs; rewrite re_rename in Hbs.
    destruct c as [[st i] o], c' as [[st' i'] o'], r as [f [g [Hinv1 Hinv2]]]; simpl in Hbs.
    do 2 (try rewrite Renaming.re_rename_state in Hbs; intuition).
    all: eapply Hinv.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    pose proof (Renaming.renaming_inv r) as [r' Hr].
    split; intros []; eexists.
    - eapply renaming_invariant_bs in H; simpl in H; apply H.
    - replace s with (rename r' (rename r s)) by (apply re_rename; assumption).
      eapply renaming_invariant_bs in H; simpl in H; apply H.
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
    - destruct k; inversion DEF; subst;
          [apply IHEXEC; intuition | apply SmokeTest.seq_assoc; apply IHEXEC; intuition].
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
    - destruct k; inversion DEF; subst;
      [ inversion EXEC; subst; apply bs_While_False; assumption 
      | 
        eapply bs_Seq; [ 
          apply bs_While_False; assumption 
        | 
          apply IHEXEC; reflexivity 
        ] 
      ].
    Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  eapply cps_bs_gen with (S1 := !s1) (k := !s2).
  - eexact STEP.
  - simpl.
    reflexivity.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
  eapply cps_bs_gen with (S1 := !s) (k := KEmpty).
  - eexact STEP.
  - simpl.
    reflexivity.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1.
  - destruct k2; destruct k3; inversion STEP; subst.
  constructor.
  - destruct k2.
    + apply STEP.
    + apply cps_Seq. apply STEP.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  inversion_clear STEP. 
  generalize dependent c3.
  generalize dependent k.
  dependent induction EXEC; intros.
  - apply cps_Skip; auto.
  - eapply cps_Assign; eauto.
  - apply cps_Read. assumption.
  - eapply cps_Write; eauto.
  - apply cps_Seq; apply IHEXEC1; destruct k; try(apply cps_Seq); eauto.
  - apply cps_If_True; eauto.
  - apply cps_If_False; eauto.
  - apply cps_While_True; eauto. apply IHEXEC1. destruct k; try(apply cps_Seq); eauto.
  - apply cps_While_False.
    all: auto.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont with (k := KEmpty).
  - eexact EXEC.
  - apply cps_Skip.
    apply cps_Empty.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
