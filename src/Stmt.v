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
Proof.
  unfold contextual_equivalent in H.
  apply (H Hole).
Qed.

Lemma eval_equiv_weaker_helper l c i o (H: l / (Id 0) => 1%Z) : 
  ~(bs_int (WHILE Var (Id 0) DO WRITE (Nat 0);; (Id 0 ::= Nat 1) END) (l, i, o) c).
Proof.
  unfold not. intros H1. dependent induction H1.
  - inversion H1_. subst. 
    inversion STEP1. subst. inversion VAL. subst. inversion STEP2. subst. inversion VAL0. subst.
    eapply IHbs_int2.
    3: constructor.
    2: reflexivity.
    constructor.
  - inversion CVAL. subst.
    assert (HE: (1 = 0)%Z). { eapply state_deterministic; eassumption. }
    discriminate.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. 
  exists (WRITE (Nat 0);;Assn (Id 0) (Nat 0)), (WRITE (Nat 0);;Assn (Id 0) (Nat 1)).
  split.
  - unfold eval_equivalent. intros. split;
     intros; inversion H; inversion H0; subst; inversion STEP1; subst; inversion VAL; subst;
      inversion STEP2; subst; inversion VAL0; subst;
      unfold eval; eexists;
      repeat econstructor.
  - unfold not. intros. unfold "~c~" in H. 
    remember (SeqR (Assn (Id 0) (Nat 1)) (WhileC (Var (Id 0)) Hole)) as ctx.
    specialize H with ctx.
    unfold eval_equivalent in H. specialize H with ([]) ([0%Z]). destruct H.
    assert (HT: <| (plug ctx (WRITE (Nat 0);; Assn (Id 0) (Nat 0))) |> [] => [0%Z]).
    * subst. econstructor. econstructor.
      + repeat constructor.
      + eapply bs_While_True.
        -- repeat constructor.
        -- repeat econstructor.
        -- apply bs_While_False.
           repeat constructor.
    * apply H in HT. subst. inversion HT. inversion H1. subst. inversion STEP1. subst.
      inversion VAL. subst.
      specialize eval_equiv_weaker_helper.
      intros HN. unfold not in HN. eapply HN.
      2: apply STEP2.
      constructor.
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
    unfold bs_equivalent. intros c c'.
    split; intros H.
    - inversion H; subst.
      inversion STEP1; subst.
      eapply bs_Seq; [eassumption | eapply bs_Seq; eassumption].
    - inversion H; subst.
      inversion STEP2; subst.
      eapply bs_Seq; [eapply bs_Seq; eassumption | eassumption].
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
    Proof.
    unfold bs_equivalent. intros c c'.
    split; intros H.
    - inversion H; subst.
      + apply bs_If_True.
        * assumption.
        * eapply bs_Seq; eassumption.
      + apply bs_If_False.
        * assumption.
        * apply bs_Skip.
    - inversion H; subst.
      + 
        inversion STEP; subst.
        eapply bs_While_True; eassumption.
      + inversion STEP; subst.
        apply bs_While_False; assumption.
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
    - apply IHEXE2; auto.
    - injection Heqloop as Heqloop; injection Heqfinal as Heqfinal.
      subst. assumption.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
    Proof.
    unfold bs_equivalent. intros c c'.
    split; intros H.
    - exfalso.
      remember (WHILE (Nat 1) DO SKIP END) as loop.
      induction H; try discriminate.
      + apply IHbs_int2. assumption.
      + injection Heqloop as Heqloop. subst.
        inversion CVAL.
    - exfalso.
      inversion H; subst; inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
    Proof.
    unfold bs_equivalent in *.
    intros c c'.
    split; intros H.
    - remember (WHILE e DO s1 END) as W1.
      induction H; try discriminate.
      + injection HeqW1 as HeqW1; subst.
        eapply bs_While_True.
        * eassumption.
        * apply EQ. eassumption.
        * apply IHbs_int2. reflexivity.
      + injection HeqW1 as HeqW1; subst.
        eapply bs_While_False. eassumption.
    - remember (WHILE e DO s2 END) as W2.
      induction H; try discriminate.
      + injection HeqW2 as HeqW2; subst.
        eapply bs_While_True.
        * eassumption.
        * apply EQ. eassumption.
        * apply IHbs_int2. reflexivity.
      + injection HeqW2 as HeqW2; subst.
        eapply bs_While_False. eassumption.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
    Proof.
    intro H.
    remember (WHILE (Nat 1) DO s END) as loop.
    induction H; try discriminate.
    - apply IHbs_int2. assumption.
    - injection Heqloop as Heqloop. subst.
      inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent in *. intros c c'.
  split; intros H.
  - inversion H; subst.
    eapply bs_Seq.
    + eassumption.
    + apply EQ. assumption.
  - inversion H; subst.
    eapply bs_Seq.
    + eassumption.
    + apply EQ. assumption.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent in *. intros c c'.
  split; intros H.
  - inversion H; subst.
    eapply bs_Seq.
    + apply EQ. eassumption.
    + eassumption.
  - inversion H; subst.
    eapply bs_Seq.
    + apply EQ. eassumption.
    + eassumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent in *. intros c c'.
  split; intros H.
  - inversion H; subst.
    + apply bs_If_True; assumption.
    + apply bs_If_False.
      * assumption.
      * apply EQ. assumption.
  - inversion H; subst.
    + apply bs_If_True; assumption.
    + apply bs_If_False.
      * assumption.
      * apply EQ. assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent in *. intros c c'.
  split; intros H.
  - inversion H; subst.
    + apply bs_If_True.
      * assumption.
      * apply EQ. assumption.
    + apply bs_If_False; assumption.
  - inversion H; subst.
    + apply bs_If_True.
      * assumption.
      * apply EQ. assumption.
    + apply bs_If_False; assumption.
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
  split. {apply eq_congruence_seq_r. assumption. }
  split. {apply eq_congruence_seq_l. assumption. }
  split. {apply eq_congruence_cond_else. assumption. }
  split. 
  - apply eq_congruence_cond_then. assumption. 
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
  generalize dependent c2. induction EXEC1; intros; inversion EXEC2; try reflexivity.
  - f_equal. f_equal. f_equal. apply eval_deterministic with e s; assumption.
  - f_equal. f_equal. f_equal. apply eval_deterministic with e s; assumption.
  - specialize IHEXEC1_1 with c'0. apply IHEXEC1_1 in STEP1. rewrite <- STEP1 in *.
    apply IHEXEC1_2. apply STEP2.
  - apply IHEXEC1. assumption.
  - assert (Z.one = Z.zero). { apply eval_deterministic with e s; assumption. } discriminate.
  - assert (Z.one = Z.zero). { apply eval_deterministic with e s; assumption. } discriminate.
  - apply IHEXEC1. assumption.
  - specialize IHEXEC1_1 with c'0. apply IHEXEC1_1 in STEP. rewrite <- STEP in *.
    apply IHEXEC1_2. apply WSTEP.
  - assert (Z.one = Z.zero). { apply eval_deterministic with e st; assumption. } discriminate.
  - assert (Z.one = Z.zero). { apply eval_deterministic with e st; assumption. } discriminate.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

(* couldn't come up with a proof *)
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
    dependent induction s;
    dependent destruction EXEC1; dependent destruction EXEC2;
    try by_eval_deterministic + eval_zero_not_one + reflexivity;
    try (specialize (IHs1 _ _ _ EXEC1 EXEC2); inversion IHs1; subst; reflexivity).
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
    Proof.
    generalize dependent c''.
    induction STEP1; intros;
    inversion STEP2; subst;
    let H2 := fresh "H2" in
    remember (ss_int_step_deterministic s c _ _ H H0) as H2;
    inversion H2; subst; try reflexivity;
    try (specialize (IHSTEP1 _ H1); assumption).
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    dependent induction s; dependent destruction STEP; 
    eauto using bs_Skip, bs_Assign, bs_Read, bs_Write.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    induction STEP1.
    - eapply ss_int_Step; [apply ss_Seq_Compl; eauto | auto].
    - eapply ss_int_Step; [apply ss_Seq_InCompl; eauto | 
      apply IHSTEP1 in STEP2; auto].
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
    induction s; intros; inversion STEP; intros; subst.
    - apply bs_Seq with (c':=c').
      + apply ss_bs_base. assumption.
      + assumption.
    - inversion EXEC; subst. apply (IHs1 c'0 c' c s1') in SSTEP.
      + apply bs_Seq with (c':=c'0). assumption. assumption.
      + assumption.
    - constructor. assumption. assumption.
    - apply bs_If_False. assumption. assumption.
    - inversion EXEC; subst; destruct c'', p.
      + inversion STEP0; subst. apply (bs_While_True ) with (c':=c').
        assumption. assumption. assumption.
      + inversion STEP0; subst. apply bs_While_False. assumption.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split.
    - intro. induction H.
      1-4: try econstructor; try econstructor; auto.
      + apply ss_ss_composition with c'. auto. auto.
      + eapply ss_int_Step. econstructor. auto. auto.
      + eapply ss_int_Step. apply ss_If_False. auto. auto.
      + eapply ss_int_Step.
        * econstructor.
        * eapply ss_int_Step. econstructor. auto. 
          eapply ss_ss_composition. eauto. auto.
      + eapply ss_int_Step. econstructor. eapply ss_int_Step. apply ss_If_False. auto.
        econstructor. econstructor.
    - intro. induction H.
      + apply ss_bs_base. auto.
      + eapply ss_bs_step. eauto. eauto. 
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
    induction s; 
    try reflexivity;
    simpl;
    try rewrite Renaming.re_rename_expr;
    try rewrite Hinv;
    try rewrite IHs1, IHs2;
    try rewrite IHs;
    try assumption;
    try reflexivity.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. destruct r. simpl. unfold update. reflexivity. Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r as [f Hbij].
    induction Hbs; simpl.
    - apply bs_Skip.
    - apply bs_Assign.
      apply Renaming.eval_renaming_invariance. assumption.
    - apply bs_Read.
    - apply bs_Write.
      apply Renaming.eval_renaming_invariance. assumption.
    - eapply bs_Seq; eauto.
    - apply bs_If_True.
      + apply Renaming.eval_renaming_invariance; eauto.
      + eauto.
    - apply bs_If_False.
      + apply Renaming.eval_renaming_invariance; eauto.
      + eauto.
    - eapply bs_While_True.
      + apply Renaming.eval_renaming_invariance; eauto.
      + eauto.
      + eauto.
    - apply bs_While_False.
      apply Renaming.eval_renaming_invariance. assumption.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    remember (Renaming.renaming_inv r) as inv_res.
    destruct inv_res as [r_inv Hinv].
    apply (renaming_invariant_bs _ r_inv) in Hbs.
    rewrite (re_rename r_inv r) in Hbs.
    - destruct c as [[st i] o].
      destruct c' as [[st' i'] o'].
      simpl in Hbs.
      rewrite Renaming.re_rename_state in Hbs; auto.
      rewrite Renaming.re_rename_state in Hbs; auto.
    - assumption.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent, eval.
    split; intro H; destruct H as [st EXECUTION].
    - exists (Renaming.rename_state r st).
      pose proof (renaming_invariant_bs s r ([], i, []) (st, [], o) EXECUTION) as PROOF_FORWARD.
      simpl in PROOF_FORWARD.
      exact PROOF_FORWARD.
    - destruct (Renaming.renaming_inv r) as [r_inv inv_prop].
      exists (Renaming.rename_state r_inv st).
      assert (STMT_EQ: rename r_inv (rename r s) = s).
      { apply re_rename; exact inv_prop. }
      rewrite <- STMT_EQ.
      pose proof (renaming_invariant_bs (rename r s) r_inv ([], i, []) (st, [], o) EXECUTION) as PROOF_BACKWARD.
      simpl in PROOF_BACKWARD.
      exact PROOF_BACKWARD.
  Qed.
  
End Renaming.


(* NOT NEED FOR E Grade *)
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
Proof. admit. Admitted.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. admit. Admitted.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. admit. Admitted.

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
