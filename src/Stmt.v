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
  specialize (H Hole). simpl in H. exact H.
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
    exists SKIP, (Id 1 ::= Nat 0); split.
  - intros i o; split; intros [st EX].
    + inversion EX; subst; exists ([] [Id 1 <- 0%Z]); apply bs_Assign, bs_Nat.
    + inversion EX; subst; exists ([] : state Z); apply bs_Skip.
  - intro CEQ; specialize (CEQ (SeqL Hole (WHILE (Var (Id 1)) DO SKIP END)) ([]) ([]));
    destruct CEQ; assert (OK : <| (Id 1 ::= Nat 0) ;; (WHILE (Var (Id 1)) DO SKIP END) |> ([]) => ([])).
    { exists ([] [Id 1 <- 0%Z]).
      apply bs_Seq with (([]) [Id 1 <- 0%Z], [], []).
      - apply bs_Assign, bs_Nat.
      - apply bs_While_False.
        apply bs_Var, st_binds_hd. }
    apply H0 in OK; destruct OK.
    inversion H1; subst.
    inversion STEP1; subst; inversion STEP2; subst; inversion CVAL; subst; inversion VAR.
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
    unfold bs_equivalent; intros c c'; split; intro H.
    - (* => *) inversion_clear H; inversion_clear STEP1; eauto.
    - (* <= *) inversion_clear H; inversion_clear STEP2; eauto.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent; intros c c'; split; intro H.
    - (* => *) inversion_clear H; eauto.
    - (* <= *) inversion_clear H; [inversion_clear STEP | inversion_clear STEP]; eauto.
  Qed.
      
  Fixpoint while_false_go (e : expr) (s : stmt) (c cfin : conf) (EXEC : c == WHILE e DO s END ==> cfin) {struct EXEC}
           :[| e |] (let '(st, _, _) := cfin in st) => Z.zero :=
    match EXEC with
    | bs_While_False st' i' o' e' s' CVAL => CVAL
    | bs_While_True st' i' o' c' cfin' e' s' CVAL STEP WSTEP =>
        while_false_go e' s' c' cfin' WSTEP
    end.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    simpl. apply (while_false_go e s c (st, i, o) EXE).
  Qed.

  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. 
    unfold bs_equivalent. intros c c'. split; intro EXE. (*Show.*)
  - (* => *)
    destruct c' as [[st x] o].
    pose proof (while_false (Nat 1) SKIP st x o c EXE) as H_f.
    inversion H_f.
  - (* <= *)
    inversion EXE; subst.
    + inversion STEP; subst. inversion CVAL.
    + inversion CVAL.
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent; intros c c'; split; intro EXE.
    - remember (WHILE e DO s1 END) as loop eqn:H_loop.
      induction EXE; try discriminate; inversion H_loop; subst.
      + apply EQ in EXE1.
        assert (NEXT: c' == WHILE e DO s2 END ==> c'') by (apply IHEXE2; reflexivity).
        eapply bs_While_True; eauto.
      + eapply bs_While_False; eauto.
    - remember (WHILE e DO s2 END) as loop eqn:H_loop.
      induction EXE; try discriminate; inversion H_loop; subst.
      + apply EQ in EXE1.
        assert (NEXT: c' == WHILE e DO s1 END ==> c'') by (apply IHEXE2; reflexivity).
        eapply bs_While_True; eauto.
      + eapply bs_While_False; eauto.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. 
    destruct c' as [[st x] o]. intro EXE.
    pose proof (while_false (Nat 1) s st x o c EXE) as HF. inversion HF.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
unfold bs_equivalent; intros c c'; split; intro H.
  - (* => *)
    inversion H; subst.
    apply EQ in STEP2.
    eauto.
  - (* <= *)
    inversion H; subst.
    apply EQ in STEP2.
    eauto.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent; intros c c'; split; intro H.
  - (* => *)
    inversion H; subst.
    apply EQ in STEP1.
    eauto.
  - (* <= *)
    inversion H; subst.
    apply EQ in STEP1.
    eauto.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent; intros c c'; split; intro H.
  - (* => *)
    inversion H; subst.
    +eauto.
    + apply EQ in STEP. eauto.
  - (* <= *)
    inversion H; subst.
    + eauto.
    + apply EQ in STEP. eauto.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent; intros c c'; split; intro H.
  - (* => *)
    inversion H; subst.
    + apply EQ in STEP. eauto.
    + eauto.
  - (* <= *)
    inversion H; subst.
    + apply EQ in STEP. eauto.
    + eauto.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  unfold bs_equivalent; intros c c'; split; intro EXE.
  - (* => *)
    remember (WHILE e DO s1 END) as loop eqn:H_loop.
    induction EXE; try discriminate; inversion H_loop; subst.
    + apply EQ in EXE1.
      assert (NEXT: c' == WHILE e DO s2 END ==> c'') by (apply IHEXE2; reflexivity).
      eapply bs_While_True; eauto.
    + eapply bs_While_False; eauto.
  - (* <= *)
    remember (WHILE e DO s2 END) as loop eqn:H_loop.
    induction EXE; try discriminate; inversion H_loop; subst.
    + apply EQ in EXE1.
      assert (NEXT: c' == WHILE e DO s1 END ==> c'') by (apply IHEXE2; reflexivity).
      eapply bs_While_True; eauto.
    + eapply bs_While_False; eauto.
Qed.

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
        apply eq_congruence_cond_then. exact EQ. 
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
Proof. 
  generalize dependent c2.
  induction EXEC1; intros c2 EXEC2;
    inversion EXEC2; subst.
  - reflexivity.
  - pose proof (eval_deterministic e s z z0 VAL VAL0). subst. reflexivity.
  - reflexivity.
  - pose proof (eval_deterministic e s z z0 VAL VAL0). subst. reflexivity.
  - assert (c' = c'0) as EQ.
    { apply IHEXEC1_1. exact STEP1. } subst. apply IHEXEC1_2. exact STEP2.
  - apply IHEXEC1. exact STEP.
  - exfalso. pose proof (eval_deterministic e s Z.one Z.zero CVAL CVAL0). discriminate.
  - exfalso. pose proof (eval_deterministic e s Z.zero Z.one CVAL CVAL0). discriminate.
  - apply IHEXEC1. exact STEP.
  - assert (c' = c'0) as EQ.
    { apply IHEXEC1_1. exact STEP. } subst. apply IHEXEC1_2. exact WSTEP.
  - exfalso. pose proof (eval_deterministic e st Z.one Z.zero CVAL CVAL0). discriminate.
  - exfalso. pose proof (eval_deterministic e st Z.zero Z.one CVAL CVAL0). discriminate.
  - reflexivity.
Qed.

Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

(* bs_equiv_states helper 1 *)
Lemma equiv_states_eval (e : expr) (s1 s2 : state Z) (z : Z) (HE : equivalent_states s1 s2)
      (H  : [| e |] s1 => z) : [| e |] s2 => z.
Proof.
  induction H; econstructor; eauto; destruct (HE i z). apply H; assumption.
Qed.

(* bs_equiv_states helper 2 *)
Lemma equiv_states_update (s1 s2 : state Z) (x : id) (z : Z) (HE : equivalent_states s1 s2) :
  equivalent_states (s1 [x <- z]) (s2 [x <- z]).
Proof.
  intros y w; split; intro HB.
  - destruct (HE y w); inversion HB; subst; [ apply st_binds_hd | apply st_binds_tl; auto ].
  - destruct (HE y w); inversion HB; subst; [ apply st_binds_hd | apply st_binds_tl; auto ].
Qed.

(* bs_equiv_states helper 3 *)
Lemma bs_equiv_states_gen (s : stmt) (c c' : conf)
      (H : c == s ==> c') :
  forall (t1 t1' : state Z) (li lo : list Z)
         (HC  : c = (t1, li, lo))
         (HEQ : equivalent_states t1 t1'),
  exists (t2 t2' : state Z) (li' lo' : list Z),
    c' = (t2, li', lo') /\ equivalent_states t2 t2' /\
    (t1', li, lo) == s ==> (t2', li', lo').
Proof.
  induction H; intros t1 t1' li lo HC HEQ.
  - (* skip *) subst; do 4 eexists; split; [ reflexivity | split; [ exact HEQ | apply bs_Skip ] ].
  - (* assign *) inversion HC; subst; do 4 eexists; split; [ reflexivity | split ].
    + apply equiv_states_update. exact HEQ.
    + apply bs_Assign. eapply equiv_states_eval; eauto.
  - (* read *) inversion HC; subst; do 4 eexists; split; [ reflexivity | split ].
    + apply equiv_states_update. exact HEQ.
    + apply bs_Read.
  - (* write *) inversion HC; subst; do 4 eexists; split; [ reflexivity | split; [ exact HEQ | ] ];
    apply bs_Write; eapply equiv_states_eval; eauto.
  - (* seq *) subst; edestruct IHbs_int1 as (m & m' & mi & mo & -> & HEm & RUN1); eauto;
    edestruct IHbs_int2 as (f & f' & fi & fo & -> & HEf & RUN2); eauto;
    do 4 eexists; split; [ reflexivity | split; [ exact HEf | ] ].
    apply bs_Seq with (m', mi, mo); assumption.
  - (* ite t *)
    inversion HC; subst.
    edestruct IHbs_int as (f & f' & fi & fo & -> & HEf & RUN); eauto; do 4 eexists;
    split; [ reflexivity | split; [ exact HEf | ] ].
    apply bs_If_True; [ eapply equiv_states_eval; eauto | exact RUN ].
  - (* ite f *) inversion HC; subst; 
    edestruct IHbs_int as (f & f' & fi & fo & -> & HEf & RUN); eauto.
    do 4 eexists; split; [ reflexivity | split; [ exact HEf | ] ].
    apply bs_If_False; [ eapply equiv_states_eval; eauto | exact RUN ].
  - (* while t *) inversion HC; subst;
    edestruct IHbs_int1 as (m & m' & mi & mo & -> & HEm & RUN1); eauto.
    edestruct IHbs_int2 as (f & f' & fi & fo & -> & HEf & RUN2); eauto.
    do 4 eexists.
    split; [ reflexivity | split; [ exact HEf | ] ].
    apply bs_While_True with (m', mi, mo);
      [ eapply equiv_states_eval; eauto | exact RUN1 | exact RUN2 ].
  - (* while f *) inversion HC; subst; do 4 eexists; split; [ reflexivity | split; [ exact HEQ | ] ].
    apply bs_While_False. eapply equiv_states_eval; eauto.
Qed.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')  
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.
  destruct (bs_equiv_states_gen s _ _ H st1 st1' i o Logic.eq_refl HE1) as (t1 & t2 & li & lo & H_eq1 & H_eq2 & H_run). (*Show.*)
  inversion H_eq1; subst; exists t2; split; assumption.
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
    induction EXEC1; intros c'' EXEC2;
    inversion EXEC2; subst.
    - reflexivity.
    - pose proof (eval_deterministic e s z z0 SVAL SVAL0); subst; reflexivity.
    - reflexivity.
    - pose proof (eval_deterministic e s z z0 SVAL SVAL0); subst; reflexivity.
    - specialize (IHEXEC1 _ SSTEP). inversion IHEXEC1; reflexivity.
    - specialize (IHEXEC1 _ SSTEP). inversion IHEXEC1.
    - specialize (IHEXEC1 _ SSTEP). inversion IHEXEC1.
    - specialize (IHEXEC1 _ SSTEP). inversion IHEXEC1; reflexivity.
    - reflexivity.
    - exfalso; pose proof (eval_deterministic e s Z.one Z.zero SCVAL SCVAL0); discriminate.
    - exfalso; pose proof (eval_deterministic e s Z.zero Z.one SCVAL SCVAL0); discriminate.
    - reflexivity.
    - reflexivity.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''. induction STEP1; intros c_final STEP2; inversion STEP2; subst.
    all: repeat match goal with
      | [ H1 : ?C -- ?S --> (?X, ?Y), H2 : ?C -- ?S --> (?Unit, ?Z) |- _ ] =>
          assert (H_eq : (X, Y) = (Unit, Z)) by (eapply ss_int_step_deterministic; eauto);
          inversion H_eq; subst; clear H_eq H1
      end; try reflexivity. apply IHSTEP1. assumption.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. 
    inversion STEP; subst.
    - (* skip *) econstructor.
    - (* assign *) econstructor. exact SVAL.
    - (* read *) econstructor.
    - (* write *) econstructor. exact SVAL.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    generalize dependent s2. generalize dependent c'.
    induction STEP1; intros c''' s2 STEP2.
    - eapply ss_int_Step; [apply ss_Seq_Compl; exact H | exact STEP2].
    - eapply ss_int_Step; [apply ss_Seq_InCompl; exact H | apply IHSTEP1; exact STEP2].
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    remember (Some s', c') as R eqn:HR.
    revert s' c' c'' HR EXEC.
    induction STEP; intros t1 t2 t3 HR EXEC; inversion HR; subst.
    - apply bs_Seq with t2; [ apply ss_bs_base; eassumption | exact EXEC ].
    - inversion EXEC; subst; eapply bs_Seq; [ eapply IHSTEP; [ reflexivity | eassumption ] | eassumption ].
    - apply bs_If_True; assumption.
    - apply bs_If_False; assumption.
    - inversion EXEC; subst.
      + seq_inversion; eapply bs_While_True; eauto.
      + match goal with
        | HS : _ == SKIP ==> _ |- _ => inversion HS; subst
        end; apply bs_While_False; assumption.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. 
        split; intro H.
    - (* => *) induction H.
      + apply ss_int_Base, ss_Skip.
      + apply ss_int_Base, ss_Assign; assumption.
      + apply ss_int_Base, ss_Read.
      + apply ss_int_Base, ss_Write; assumption.
      + eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step; [ apply ss_If_True; eassumption | assumption ].
      + eapply ss_int_Step; [ apply ss_If_False; eassumption | assumption ].
      + eapply ss_int_Step; [ apply ss_While | ].
        eapply ss_int_Step; [ apply ss_If_True; eassumption | ].
        eapply ss_ss_composition; eassumption.
      + eapply ss_int_Step; [ apply ss_While | ].
        eapply ss_int_Step; [ apply ss_If_False; eassumption | ].
        apply ss_int_Base, ss_Skip.
    - (* <= *) induction H.
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
    induction s; simpl.
    - reflexivity.
    - rewrite Hinv. rewrite Renaming.re_rename_expr; auto.
    - rewrite Hinv. reflexivity.
    - rewrite Renaming.re_rename_expr; auto.
    - rewrite IHs1, IHs2. reflexivity.
    - rewrite Renaming.re_rename_expr; auto.
      rewrite IHs1, IHs2. reflexivity.
    - rewrite Renaming.re_rename_expr; auto.
      rewrite IHs. reflexivity.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    destruct r as [f Hf]. simpl. reflexivity.
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r. induction Hbs; simpl.
    - apply bs_Skip.
    - apply bs_Assign; apply Renaming.eval_renaming_invariance; assumption.
    - apply bs_Read.
    - apply bs_Write; apply Renaming.eval_renaming_invariance; assumption.
    - eapply bs_Seq; eassumption.
    - apply bs_If_True; [ apply Renaming.eval_renaming_invariance; assumption | assumption ].
    - apply bs_If_False; [ apply Renaming.eval_renaming_invariance; assumption | assumption ].
    - eapply bs_While_True; [ apply Renaming.eval_renaming_invariance; assumption | eassumption | eassumption ].
    - apply bs_While_False; apply Renaming.eval_renaming_invariance. assumption.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    destruct (Renaming.renaming_inv r). (*Show.*)
    assert (REV : forall c0 : conf, rename_conf x (rename_conf r c0) = c0).
    { intros [[s0 i0] o0]; simpl; now rewrite (Renaming.re_rename_state x r H). }
    apply (renaming_invariant_bs _ x) in Hbs.
    rewrite (re_rename x r H) in Hbs; rewrite !REV in Hbs; exact Hbs.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    intros i o; split; intros [s' H].
    - exists (Renaming.rename_state r s'). exact (renaming_invariant_bs s r ([], i, []) (s', [], o) H).
    - destruct (Renaming.renaming_inv2 r). (*Show.*)
      exists (Renaming.rename_state x s').
      apply (renaming_invariant_bs_inv s r ([], i, []) (Renaming.rename_state x s', [], o)); simpl.
      now rewrite (Renaming.re_rename_state r x H0).
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
    induction EXEC in S, DEF.
  - (* empty *) discriminate DEF.
  - (* skip *)
    destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst; apply bs_Skip.
    + apply bs_Seq with c; [ apply bs_Skip | apply IHEXEC; reflexivity ].
  - (* assign *)
    destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst; apply bs_Assign; assumption.
    + apply bs_Seq with ((s) [x <- n], i, o); [ apply bs_Assign; assumption | apply IHEXEC; reflexivity ].
  - (* read *)
    destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst; apply bs_Read.
    + apply bs_Seq with ((s) [x <- z], i, o); [ apply bs_Read | apply IHEXEC; reflexivity ].
  - (* write *)
    destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst; apply bs_Write; assumption.
    + apply bs_Seq with (s, i, z :: o); [ apply bs_Write; assumption | apply IHEXEC; reflexivity ].
  - (* seq *)
    destruct k; simpl in DEF; inversion DEF; subst.
    + apply IHEXEC; reflexivity.
    + assert (LIN: c == s1 ;; (s2 ;; s) ==> c') by (apply IHEXEC; reflexivity);
      inversion LIN; subst; inversion STEP2; subst; eapply bs_Seq; [ eapply bs_Seq; eassumption | eassumption ].
  - (* ite t *)
    destruct k; simpl in DEF; inversion DEF; subst.
    + apply bs_If_True; [ assumption | apply IHEXEC; reflexivity ].
    + assert (REST: (s, i, o) == s1 ;; s0 ==> c') by (apply IHEXEC; reflexivity).
      inversion REST; subst.
      eapply bs_Seq; [ apply bs_If_True; eassumption | eassumption ].
  - (* ite f *)
    destruct k; simpl in DEF; inversion DEF; subst.
    + apply bs_If_False; [ assumption | apply IHEXEC; reflexivity ].
    + assert (REST: (s, i, o) == s2 ;; s0 ==> c') by (apply IHEXEC; reflexivity).
      inversion REST; subst.
      eapply bs_Seq; [ apply bs_If_False; eassumption | eassumption ].
  - (* while t *)
    destruct k; simpl in DEF; inversion DEF; subst.
    + assert (BODY: (st, i, o) == s ;; (WHILE e DO s END) ==> c') by (apply IHEXEC; reflexivity).
      inversion BODY; subst.
      eapply bs_While_True; eassumption.
    + assert (BODY: (st, i, o) == s ;; ((WHILE e DO s END) ;; s0) ==> c') by (apply IHEXEC; reflexivity).
      inversion BODY; subst; inversion STEP2; subst.
      eapply bs_Seq; [ eapply bs_While_True; eassumption | eassumption ].
  - (* while f *)
    destruct k; simpl in DEF; inversion DEF; subst.
    + inversion EXEC; subst; apply bs_While_False; assumption.
    + apply bs_Seq with (st, i, o); [ apply bs_While_False; assumption | apply IHEXEC; reflexivity ].
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  eapply cps_bs_gen.
  - eauto.
  - reflexivity. 
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
  eapply cps_bs_gen.
  - eauto.
  - reflexivity.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. 
    destruct k1; destruct k2; simpl.
  - exact STEP.
  - destruct k3; inversion STEP.
  - exact STEP.
  - apply cps_Seq.
    exact STEP.
Qed.

(* helper for next lemma *)
Lemma kapp_empty_r (k : cont) : k @ KEmpty = k.
Proof.
  destruct k; reflexivity.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  inversion STEP; subst; clear STEP; revert k c3 CSTEP; induction EXEC; intros k0 d H_k.
  - apply cps_Skip. exact H_k.
  - eapply cps_Assign; [ eassumption | exact H_k ].
  - apply cps_Read. exact H_k.
  - eapply cps_Write; [ eassumption | exact H_k ].
  - apply cps_Seq; apply IHEXEC1; apply cps_cont_to_seq; rewrite kapp_empty_r; apply IHEXEC2;
    exact H_k.
  - apply cps_If_True; [ assumption | apply IHEXEC; exact H_k ].
  - apply cps_If_False; [ assumption | apply IHEXEC; exact H_k ].
  - apply cps_While_True; [ assumption | ].
    apply IHEXEC1.
    apply cps_cont_to_seq.
    rewrite kapp_empty_r.
    apply IHEXEC2.
    exact H_k.
  - apply cps_While_False; [ assumption | exact H_k ].
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont.
  - exact EXEC.
  - apply cps_Skip; apply cps_Empty.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
