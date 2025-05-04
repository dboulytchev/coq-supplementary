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
  unfold contextual_equivalent in H. apply (H Hole).
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  exists ((Id 1) ::= (Nat 42)).
  exists ((Id 1) ::= (Nat 43)).
  split.
    {constructor; intros; inversion H; inversion H0; econstructor; eauto. }
    {unfold not. unfold contextual_equivalent. intros.
     specialize (H (SeqL Hole (WRITE (Var (Id 1))))).
     simpl in H. unfold eval_equivalent in H.
     specialize (H ([]) ([42%Z])). inversion H.
     destruct H0.
      {econstructor. 
       econstructor.
       econstructor. 
       econstructor. 
       econstructor. 
       econstructor. 
       econstructor. }
      {inversion H0. subst. 
       inversion STEP1. subst. 
       inversion VAL. subst.
       inversion STEP2. subst.
       inversion VAL0. subst.
       inversion VAR. subst.
       inversion H8. } }
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
   split; intro; seq_inversion; seq_inversion; seq_apply.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    split; intros.
    {inversion H; subst.
     {constructor. assumption. seq_apply. }
     {apply bs_If_False. assumption. constructor. } }
    {inversion H; subst; inversion STEP; subst.
     {econstructor. assumption. eauto. auto. }
     {apply bs_While_False. assumption. } }
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END) as prog.
    remember ((st, i, o)) as state.
    induction EXE; inversion Heqprog.
      {subst. apply IHEXE2; reflexivity. }
      {inversion Heqstate. subst. assumption. }
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    split; intros.
    {inversion H; subst. 
     {destruct c', p. apply while_false in H. inversion H. }
     {inversion CVAL. } }
    {inversion H; subst. inversion CVAL. inversion CVAL. }
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
   split; intros.
    {remember (WHILE e DO s1 END) in H.
     induction H; inversion Heqs; subst.
      {apply while_unfolds. constructor. assumption.
       {apply bs_Seq with (c':=c'). 
        {destruct (EQ ((st, i, o)) c'). auto. }
        {apply IHbs_int2. reflexivity. } } }
      {constructor. assumption. } }
    {remember (WHILE e DO s2 END) in H.
     induction H; inversion Heqs; subst.
      {apply while_unfolds. constructor. assumption.
       apply bs_Seq with (c':=c').
       {destruct (EQ ((st, i, o)) c'). auto. }
       {apply IHbs_int2. reflexivity. } }
      {constructor. assumption. } }
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
   unfold not. intros.
   remember (WHILE Nat 1 DO s END) in H.
   induction H; inversion Heqs0; subst.
    {apply IHbs_int2. reflexivity. }
    {inversion CVAL. }
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  constructor; intros; inversion H; subst; 
  apply bs_Seq with (c':=c'0).
    {assumption. }
    {apply EQ. assumption. }
    {assumption. }
    {apply EQ. assumption. }
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
  Proof.
    constructor; intros; inversion H; subst; 
    apply bs_Seq with (c':=c'0).
      {apply EQ. assumption. }
      {assumption. }
      {apply EQ. assumption. }
      {assumption. }
  Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. 
  constructor; intros; inversion H.
    {constructor. assumption. assumption. }
    {apply bs_If_False. 
     {assumption. }
     {apply EQ. assumption. } }
    {constructor. assumption. assumption. }
    {apply bs_If_False. 
     {assumption. }
     {apply EQ. assumption. } }
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  constructor; intros; inversion H.
   {apply bs_If_True.
    {assumption. }
    {apply EQ. assumption. } }
   {apply bs_If_False. assumption. assumption. }
   {apply bs_If_True.
    {assumption. }
    {apply EQ. assumption. } }
   {apply bs_If_False. assumption. assumption. }
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
  split. apply eq_congruence_seq_r. assumption.
  split. apply eq_congruence_seq_l. assumption.
  split. apply eq_congruence_cond_else. assumption.
  split. apply eq_congruence_cond_then. assumption.
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
  generalize dependent c2.
  induction EXEC1; intros; inversion EXEC2; subst.
   {eauto. }
   {by_eval_deterministic. }
   {eauto. }
   {by_eval_deterministic. }
   {assert (c' = c'0). 
    { apply IHEXEC1_1. assumption. }
    {apply IHEXEC1_2. rewrite H. assumption. } }
   {eauto. }
   {eval_zero_not_one. }
   {eval_zero_not_one. }
   {eauto. }
   {assert (c' = c'0). 
    { apply IHEXEC1_1. assumption. }
    {apply IHEXEC1_2. rewrite H. assumption. } } 
   {eval_zero_not_one. }
   {eval_zero_not_one. }
   {eauto. }
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
    induction EXEC1; intros; inversion EXEC2; subst; auto.
      {by_eval_deterministic. }
      {by_eval_deterministic. }
      {apply IHEXEC1 in SSTEP. inversion SSTEP. reflexivity. }
      {apply IHEXEC1 in SSTEP. inversion SSTEP. }
      {apply IHEXEC1 in SSTEP. inversion SSTEP. }
      {apply IHEXEC1 in SSTEP. inversion SSTEP. reflexivity. }
      {eval_zero_not_one. }
      {eval_zero_not_one. }
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    generalize dependent c''.
    induction STEP1; intros; inversion STEP2; subst; auto.
    {apply (ss_int_step_deterministic s c (None, c') (None, c'')) in H; eauto. 
     inversion H. reflexivity. }
    {apply (ss_int_step_deterministic s c (None, c') (Some s', c'0)) in H; eauto. 
     inversion H. }
    {apply (ss_int_step_deterministic s c (Some s', c') (None, c''0)) in H; eauto. 
     inversion H. }
    {apply (ss_int_step_deterministic s c (Some s', c') (Some s'0, c'0)) in H; eauto. 
     inversion H. subst. apply IHSTEP1. assumption. }
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
   inversion STEP; constructor; assumption.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
    generalize dependent c'. induction STEP1; intros.
    {apply (ss_int_Step _ s2 _ c'). constructor. assumption. assumption. }
    {apply (ss_int_Step _ (s' ;; s2) _ c'). constructor. 
     {assumption. }
     {apply IHSTEP1. assumption. } }
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
     {apply bs_Seq with (c':=c').
      {apply ss_bs_base. assumption. }
      {assumption. } }
     {inversion EXEC; subst. apply (IHs1 c'0 c' c s1') in SSTEP.
      {apply bs_Seq with (c':=c'0). assumption. assumption. }
      {assumption. } }
     {constructor. assumption. assumption. }
     {apply bs_If_False. assumption. assumption. }
     {inversion EXEC; subst.
      destruct c'', p; inversion STEP0.
       {inversion STEP0; subst. apply (bs_While_True ) with (c':=c').
        {assumption. }
        {assumption. }
        {assumption. } }
       {inversion STEP0; subst. apply bs_While_False. assumption. } }
  Qed.

  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
    split; intros; induction H.
      {constructor. constructor. }
      {constructor. constructor. assumption. }
      {constructor. constructor. }
      {constructor. constructor. assumption. }
      {eapply ss_ss_composition. eassumption. assumption. }
      {eapply ss_int_Step. 
        {eapply ss_If_True. assumption. }
        {assumption. } }
      {eapply ss_int_Step.
        {eapply ss_If_False. assumption. }
        {assumption. } }
      {eapply ss_int_Step.
        {eapply ss_While. }
        {eapply ss_int_Step.
          {eapply ss_If_True. assumption. }
          {eapply ss_ss_composition.
            {apply IHbs_int1. }
            {assumption. } } } }
      {eapply ss_int_Step.
        {eapply ss_While. }
        {eapply ss_int_Step.
          {eapply ss_If_False. assumption. }
          {constructor. constructor. } } }
      {eapply ss_bs_base. assumption. }
      {eapply ss_bs_step. apply H. assumption. }
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
    induction s; simpl; unfold Renaming.renamings_inv in Hinv.
      {reflexivity. }
      {rewrite Hinv. rewrite Renaming.re_rename_expr.
       {reflexivity. }
       {assumption. } }
      {rewrite Hinv. reflexivity. }
      {rewrite Renaming.re_rename_expr.
        {reflexivity. }
        {assumption. } }
      {rewrite IHs1. rewrite IHs2. reflexivity. }
      {rewrite Renaming.re_rename_expr.
        {rewrite IHs1. rewrite IHs2. reflexivity. }
        {assumption. } }
      {rewrite Renaming.re_rename_expr.
        {rewrite IHs. reflexivity. }
        {assumption. } }
  Qed.  

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. 
    simpl. unfold Renaming.rename_id. destruct r. subst. reflexivity.
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    induction Hbs; subst; simpl; destruct r.
    {eapply bs_Skip. }
    {constructor. apply Renaming.eval_renaming_invariance. assumption. }
    {eapply bs_Read. }
    {eapply bs_Write. apply Renaming.eval_renaming_invariance. assumption. }
    {econstructor. apply IHHbs1. assumption. }
    {apply bs_If_True.
     {apply Renaming.eval_renaming_invariance. assumption. }
     {assumption. } }
    {apply bs_If_False.
     {apply Renaming.eval_renaming_invariance. assumption. }
     {assumption. } }
    {eapply bs_While_True.
     {apply Renaming.eval_renaming_invariance. assumption. }
     {apply IHHbs1. }
     {apply IHHbs2. } }
    {eapply bs_While_False. apply Renaming.eval_renaming_invariance. assumption. }
  Qed. 
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    remember (Renaming.renaming_inv r) as H.
    inversion H.
    eapply renaming_invariant_bs with (r:=x) in Hbs.
    rewrite re_rename in Hbs.
    destruct c, c', p, p0; subst. 
      {simpl in Hbs.
       rewrite Renaming.re_rename_state in Hbs.
       rewrite Renaming.re_rename_state in Hbs.
       assumption. assumption. assumption.  } 
      {assumption. }
  Qed.

    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent.
    unfold eval. split; intros.
      {destruct H.
       apply renaming_invariant_bs with (r:=r) in H.
       simpl in H. exists (Renaming.rename_state r x). assumption. }
      {destruct H. remember (Renaming.renaming_inv2 r) as H1.
       inversion H1. 
       rewrite <- (Renaming.re_rename_state r x0 H0 ([])) in H.
       rewrite <- (Renaming.re_rename_state r x0 H0 x) in H.
       apply (
        renaming_invariant_bs_inv 
          s 
          r 
          ((Renaming.rename_state x0 ([])), i, []) 
          ((Renaming.rename_state x0 x), [], o)) in H.
       simpl in H.
       exists (Renaming.rename_state x0 x). assumption.
       }
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
  induction EXEC; intros; subst.
    {discriminate. }
    {cps_bs_gen_helper k DEF bs_Skip. }
    {cps_bs_gen_helper k DEF bs_Assign. }
    {cps_bs_gen_helper k DEF bs_Read. }
    {cps_bs_gen_helper k DEF bs_Write. }
    {destruct k; inversion DEF; subst.
      {eauto. }
      {apply SmokeTest.seq_assoc. eauto. } }
    {destruct k; inversion DEF; subst.
      {apply bs_If_True. assumption. eauto. }
      {assert (H : (s, i, o) == s1;; s0 ==> c').
       eauto. inversion H; subst.
       apply (bs_Seq _ c'0).
        apply bs_If_True; assumption. 
        assumption. } }
    {destruct k; inversion DEF; subst.
      {apply bs_If_False; eauto. }
      {assert (H : (s, i, o) == s2;; s0 ==> c').
       eauto. inversion H; subst.
       apply (bs_Seq _ c'0).
       apply bs_If_False; assumption. 
       assumption. } }
    {destruct k; inversion DEF; subst.
      {apply SmokeTest.while_unfolds. apply bs_If_True; eauto. }
      {assert (H: ((st, i, o)) == s;; (WHILE e DO s END);; s0 ==> (c') -> ((st, i, o)) == (WHILE e DO s END);; s0 ==> (c')).
        {intros. inversion H. subst. inversion STEP2. subst. apply (bs_Seq _ c'1).
        {apply SmokeTest.while_unfolds. apply bs_If_True; eauto. }
        {assumption. } }
        apply H. eauto. } }
    {destruct k; inversion DEF; subst.
      {inversion EXEC. apply bs_While_False. assumption. }
      {apply (bs_Seq _ (st, i, o)). eauto. eauto. } }
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. 
  eapply cps_bs_gen. eapply STEP. reflexivity.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. 
  eapply cps_bs_gen. eapply STEP. reflexivity.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. 
  destruct k1; destruct k2.
    {unfold Kapp. unfold Kapp in STEP. assumption. }
    {destruct k3.
      {unfold Kapp. unfold Kapp in STEP. inversion STEP. }
      {unfold Kapp. unfold Kapp in STEP. inversion STEP. } }
    {unfold Kapp. unfold Kapp in STEP. assumption. }
    {destruct k3.
      {unfold Kapp. unfold Kapp in STEP. apply cps_Seq.
       unfold Kapp. assumption. }
      {apply cps_Seq. assumption. } }
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  generalize dependent k.
  induction EXEC; intros; inversion STEP; subst; try (eauto).
    {apply cps_Assign with (n := z); assumption. }
    {apply cps_Read. assumption. }
    {apply cps_Write with (z:=z); assumption. }
    {apply cps_Seq. apply IHEXEC1. unfold Kapp. destruct k.
      {constructor. apply IHEXEC2. assumption. }
      {constructor. constructor. eauto. } }
    {apply cps_If_True; eauto. }
    {apply cps_If_False; eauto. }
    {apply cps_While_True. eauto.
     unfold Kapp. destruct k.
     {apply IHEXEC1. constructor. eauto. }
     {apply IHEXEC1. constructor. constructor. eauto. } }
    {apply cps_While_False; eauto. }
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont. eauto. constructor. apply cps_Empty.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
