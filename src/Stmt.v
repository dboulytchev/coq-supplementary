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
| bs_Skip        : forall (c : conf),
    c == SKIP ==> c 
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

(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf),
    c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Ltac seq_inversion :=
  match goal with
    H: _ == _ ;; _ ==> _ |- _ => inversion_clear H
  end.

Ltac seq_apply :=
  match goal with
  | H: _   == ?s1 ==> ?c' |- _ == (?s1 ;; _) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | auto]
  | H: ?c' == ?s2 ==>  _  |- _ == (_ ;; ?s2) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | auto]
  end.

Lemma bs_equivalence_sym (s1 s2 : stmt) (EQ : s1 ~~~ s2) : 
    (s2 ~~~ s1).
Proof.
  unfold bs_equivalent in EQ. unfold bs_equivalent.
  intros. apply iff_sym. apply EQ.
Qed.

Module SmokeTest.

  (* Associativity of sequential composition *)
  Lemma seq_assoc (s1 s2 s3 : stmt) :
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
    unfold bs_equivalent.
    intros.
    split.
    { 
      intro.
      inversion_clear H.
      inversion_clear STEP1.
      repeat econstructor; eauto.
    }
    {
      intro.
      inversion_clear H.
      inversion_clear STEP2.
      repeat econstructor; eauto.
    }
 Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
    unfold bs_equivalent.
    intros.
    split.
    { intro.
      inversion_clear H.
      { apply bs_If_True. auto. econstructor. eauto. auto. }
      { apply bs_If_False. auto. constructor. }
    }

    {
      intro.
      inversion_clear H.
      inversion_clear STEP.
      econstructor.
      eauto. eauto. eauto.
      destruct c'. destruct p.
      inversion STEP.
      apply bs_While_False.
      clear - H CVAL.
      subst.
      exact CVAL.
    }
  Qed.

  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.
    remember (WHILE e DO s END).
    remember (st, i, o).
    induction EXE; inversion Heqs0.
    { apply IHEXE2. auto. auto. }
    { inversion Heqp. subst. auto. }
  Qed.



  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
    unfold bs_equivalent.

    intros.
    split.
   {
     intro.
     inversion_clear H.
     inversion STEP.
     destruct c' eqn:E. destruct p.
     apply (while_false (Nat 1) SKIP s l0 l c'0) in WSTEP.
     inversion WSTEP.
     inversion CVAL.
   }

   {
      intro.
      inversion_clear H.

      1-2: 
        inversion_clear STEP;
        destruct c' eqn:E; destruct p;
        apply bs_While_False;
        inversion CVAL.
   }
Qed.


  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
     unfold bs_equivalent.
          
     split; intros;
     [ remember (WHILE e DO s1 END) | remember (WHILE e DO s2 END) ];

     induction H; inversion Heqs;
     econstructor;
     subst; eauto; subst;
     unfold bs_equivalent in EQ;
     apply EQ in H;
     eauto.
  Qed.

  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
 Proof. 
    unfold not.
    intro. 
    remember (WHILE Nat 1 DO s END). 
    induction H; inversion Heqs0; subst.
    { eapply IHbs_int2. eauto. }
    { inversion CVAL. }
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent.
  unfold bs_equivalent in EQ.
  intros c c'.
  split.

  1-2: by 
  intro H; seq_inversion; specialize (EQ c'0 c');
                    apply EQ in STEP2; seq_apply.
Qed.


Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent.
  unfold bs_equivalent in EQ.
  intros.
  split.
  
   1-2: by
   intro; seq_inversion; specialize (EQ c c'0);
                  apply EQ in STEP1; seq_apply.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  unfold bs_equivalent.
  unfold bs_equivalent in EQ.
  intros.
  split.

  1-2: by
    intros;
    inversion_clear H;
    [ eapply bs_If_True| eapply bs_If_False];
    eauto; apply EQ.
Qed.


Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.

  unfold bs_equivalent.
  unfold bs_equivalent in EQ.
  intros.
  split.

  1-2: by
    intros;
    inversion_clear H;
    [ eapply bs_If_True| eapply bs_If_False];
    eauto; apply EQ.
Qed.

Lemma eq_congruence_while
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
  apply SmokeTest.while_eq. auto.
Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
  split. apply eq_congruence_seq_r. auto.
  split. apply eq_congruence_seq_l. auto.
  split. apply eq_congruence_cond_else. auto.
  split. apply eq_congruence_cond_then. auto.
  apply eq_congruence_while. auto. auto.
Qed.

(* Big-step semantics is deterministic *)
Ltac by_eval_deterministic :=
  match goal with
    H1: [|?e|]?s => ?z1, H2: [|?e|]?s => ?z2 |- _ => 
     apply (eval_deterministic e s z1 z2) in H1; [subst z2; reflexivity | auto]
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
  induction EXEC1; intros; inversion EXEC2; auto.
  { apply (eval_deterministic e s z z0) in VAL. subst z. auto. auto. }
  { apply (eval_deterministic e s z z0) in VAL. subst z. auto. auto. }
  { apply IHEXEC1_1 in STEP1. subst c'0. apply IHEXEC1_2 in STEP2. auto. }
  { eval_zero_not_one. }
  { eval_zero_not_one. }
  { apply IHEXEC1_1 in STEP. subst c'0. apply IHEXEC1_2 in WSTEP. auto. }
  { eval_zero_not_one. }
  { eval_zero_not_one. }
Qed.

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
  forall (C : Context), (C <~ s1) ~~~ (C <~ s2).
Notation "s1 '~c~' s2" := (contextual_equivalent s1 s2)
                            (at level 42, no associativity).

(* Contextual equivalence is equivalent to the semantic one *)
(* TODO: no longer needed *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); auto.
    
Lemma eq_eq_ceq s1 s2: s1 ~~~ s2 <-> s1 ~c~ s2.
Proof.
split; intro HH.
  2: { specialize (HH Hole). simpl in *. auto. }
  red. intros. induction C; simpl in *; auto.
  all: apply eq_congruence; auto.
  all: apply (Nat 0).
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
    generalize dependent c'.
    induction EXEC2; intros.

    { inversion EXEC1. auto. }
    { 
      inversion EXEC1.
      subst.
      apply (eval_deterministic e s z z0) in SVAL.
      subst z.
      auto.
      auto.
    }
    { inversion EXEC1. auto. }
    {
      inversion EXEC1.
      auto.
      apply (eval_deterministic e s z z0) in SVAL.
      subst z.
      auto.
      auto.
    }
    { 
      inversion EXEC1.
      inversion EXEC2;
      specialize (IHEXEC2 (None, c'1));
      apply IHEXEC2 in SSTEP;
      inversion SSTEP;
      auto;
      subst c';
      auto.
      specialize (IHEXEC2 (Some s1', c'1)).
      apply IHEXEC2 in SSTEP.
      inversion SSTEP.
    }
    { 
      inversion EXEC1.
      inversion EXEC2;
      specialize (IHEXEC2 (None, c'1));
      apply IHEXEC2 in SSTEP;
      inversion SSTEP;
      auto;
      subst c';
      auto.
      specialize (IHEXEC2 (Some s1'0, c'1)).
      apply IHEXEC2 in SSTEP.
      inversion SSTEP.
      auto.
    }
    { inversion EXEC1. auto. eval_zero_not_one. }
    { inversion EXEC1. eval_zero_not_one. auto. }
    { inversion EXEC1. auto. }
   
  Qed.
(*
  generalize dependent c'.
  induction EXEC2; intros.


  { inversion EXEC1.
   
    reflexivity.
  }
  {
     inversion EXEC1.
    inversion EXEC2.
    subst.
    inversion H6.
    subst s0.
    apply (eval_deterministic e s1 z z0) in SVAL.
    subst z.
    reflexivity.
  }
  Focus 5.
  inversion EXEC1.
  inversion EXEC2.
  reflexivity.
*)
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
 Proof.
    generalize dependent c''.
    induction STEP1. 
    - intros c'' STEP2. inversion STEP2.
      + apply ss_int_step_deterministic with (c':=(None, c'')) in H.
        inversion H. reflexivity. auto.
      + apply ss_int_step_deterministic with (c':=(Some s', c'0)) in H.
        inversion H. auto.
    - intros c''0 STEP2. inversion STEP2.
      + apply ss_int_step_deterministic with (c':=(None, c''0)) in H.
        inversion H. auto.
      + apply ss_int_step_deterministic with (c':=(Some s'0, c'0)) in H.
        inversion H. subst. apply IHSTEP1 in H1. auto. auto.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
   Proof.
    remember (None, c') as c'' eqn:Heq.
    induction STEP; inversion Heq.
    { apply bs_Skip. }
    { apply bs_Assign. auto. }
    { apply bs_Read. }
    { apply bs_Write. auto. }

  Qed.


(*  (*Вспомогательная лемма*)
  Lemma ss_ss_composition' (c c'' : conf) (c' : (option stmt * conf)) 
(s1 s2 : stmt)
    (STEP1: c -- s1 --> (None, c'')) (STEP2 : c'' -- s2 --> c') :
    c -- s1 ;; s2 --> c'.

Proof.
  inversion STEP1.
  subst c''.
 apply ss_Seq_Compl.
(*Неверна!!! Без индукции доказать невозможно, *)
вычисления имеют разную длину!
admit. Admitted.
*)

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.

    generalize dependent c'.
    induction STEP1; intros c'0 Hst.
    { 
      apply ss_int_Step with (s2) (c').
      apply ss_Seq_Compl. auto. auto.
    }
    { 
      apply ss_int_Step with (s' ;; s2) (c').
      apply ss_Seq_InCompl. auto.
      apply IHSTEP1 in Hst. auto.
    }

  Qed.


  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
 Proof.
    generalize dependent EXEC.
    generalize dependent STEP.
    generalize dependent c''.
    generalize dependent c'.
    generalize dependent c.
    generalize dependent s'.

    induction s; intros s' c c' c'' STEP EXEC.
    1-4 : inversion STEP.
    {
      inversion STEP.
        { apply ss_bs_base in SSTEP. seq_apply. }
        { 
          subst s'. inversion EXEC. subst.
          apply IHs1 with (c'':=c'1) in SSTEP. seq_apply. auto.
        }
    }
    {
      inversion STEP.
      { apply bs_If_True. auto. subst. auto. }
      { apply bs_If_False. auto. subst. auto. }
    }
    { 
      inversion STEP.
      subst s'. inversion EXEC; subst.
      {
        inversion STEP0. subst.
        apply bs_While_True with (c').
        auto. auto. auto.
      }
      { 
        inversion STEP0.
        apply bs_While_False.
        auto.
      }
    }
  Qed.
  
   Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
Proof.
    split; intro.
    { induction H.
      all: try by econstructor; econstructor; auto. 
      { eapply ss_ss_composition. eauto. auto. }
        { 
          eapply ss_int_Step. apply ss_If_True.
          auto. auto.
        }
        { 
          eapply ss_int_Step. apply ss_If_False.
          auto. auto. 
        }
        { 
          eapply ss_int_Step. econstructor. eapply ss_int_Step.
            { econstructor. auto. }
            { eapply ss_ss_composition. eauto. auto. }
        }
      { eapply ss_int_Step. econstructor. eapply ss_int_Step.
        { eapply ss_If_False. auto. }
        { econstructor. econstructor. }
      }
    }
    { induction H.
      { eapply ss_bs_base. auto. }
      { eapply ss_bs_step. eauto. auto. }
    }
  Qed.

  
End SmallStep.

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
  induction EXEC; intros.
  { inversion DEF. }
  { cps_bs_gen_helper k DEF bs_Skip. }
  { cps_bs_gen_helper k DEF bs_Assign. }
  { cps_bs_gen_helper k DEF bs_Read. }
  { cps_bs_gen_helper k DEF bs_Write. }
  { 
    destruct k.
    { apply (IHEXEC S). apply DEF. }
    { inversion DEF.
      apply SmokeTest.seq_assoc.
      apply IHEXEC. auto.
    }
  }
  { 
      destruct k; inversion DEF.
    {
      subst. apply bs_If_True.
      auto. auto.
    }
    { assert ((s, i, o) == s1 ;; s0 ==> (c')).
      { apply IHEXEC. auto. }
      inversion H. subst.
      apply bs_Seq with (c'0). apply bs_If_True.
      auto. auto. auto.
    }
  }
  { 
    destruct k; inversion DEF.
    { subst. apply bs_If_False. auto. auto. }
    { assert ((s, i, o) == s2 ;; s0 ==> (c')).
      { apply IHEXEC. auto. }
      inversion H. subst.
      apply bs_Seq with (c'0). apply bs_If_False.
      auto. auto. auto.
    }
  }
  { destruct k; inversion DEF.
    {
      subst.
      assert ((st, i, o) == s ;; (WHILE e DO s END) ==> c').
      { auto. }
      inversion H. subst.
      apply bs_While_True with (c'0).
      auto. auto. auto.
    }
    { subst.
      assert ((st, i, o) == s ;; (WHILE e DO s END) ;; s0 ==> c').
      { auto. }
      inversion H. subst.
      inversion_clear STEP2. apply bs_Seq with (c'1).
      apply bs_While_True with (c'0).
      auto. auto. auto. auto.
    }
  }
  { cps_bs_gen_helper k DEF bs_While_False. }
Qed.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof.
  remember !(s1 ;; s2).
  eapply cps_bs_gen. eauto.
  unfold Kapp.
  eauto.
Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. 
  remember !(s) @ KEmpty.
  eapply cps_bs_gen.
  eauto.
  unfold Kapp.
  eauto.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1; destruct k2; unfold Kapp.
  { auto. }
  { destruct k3; unfold Kapp in STEP; inversion STEP. }
  { unfold Kapp in STEP. auto. }
  { apply cps_Seq. auto. }
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
    generalize dependent k.
    induction EXEC; intros.
    
    1-9: try by econstructor; eauto; inversion STEP.

    1-2: econstructor; eauto; destruct k; eapply IHEXEC1; 
         econstructor;
         
         [ eapply IHEXEC2 | econstructor; eapply IHEXEC2; unfold Kapp];
         
        auto.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
   induction EXEC.
   all: try by econstructor; eauto; econstructor.

  { 
    econstructor.
    eapply bs_int_to_cps_int_cont. eauto.
    econstructor.
    exact IHEXEC2.
  }
  { 
    econstructor. eauto.
    eapply bs_int_to_cps_int_cont. eauto.
    econstructor.
    exact IHEXEC2.
  }
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
