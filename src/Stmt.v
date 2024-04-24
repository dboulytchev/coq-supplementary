Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Import Coq.Program.Equality.
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
  specialize (H Hole). simpl in H. assumption.
Qed. 

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
  assert (((Id 1) ::= (Var (Id 2))) ~e~ ((Id 2) ::= (Var (Id 1)))). 
  {
    constructor; intros.
    - inversion H. inversion H0.
      inversion VAL. inversion VAR.
    - inversion H. inversion H0.
      inversion VAL. inversion VAR.
  }
  assert (~(((Id 1) ::= (Var (Id 2))) ~c~ ((Id 2) ::= (Var (Id 1))))). 
  {
    unfold not. intros.
    unfold contextual_equivalent in H0.
    specialize (H0 (SeqR (READ(Id 1)) (SeqL Hole (WRITE(Var (Id 2)))))).
    simpl in H0.
    unfold eval_equivalent in H0.
    specialize (H0 ((1%Z) :: []) ((1%Z) :: [])).
    assert (<|READ (Id 1);; (Id 2 ::= Var (Id 1));; WRITE (Var (Id 2))|> [1%Z] => ([1%Z])).
    {
      remember (([])[(Id 1) <- 1%Z]) as s'. 
      econstructor. 
      apply bs_Seq with (s', [], []).
      subst s'.
      apply bs_Read.
      apply bs_Seq with (s'[(Id 2) <- 1%Z], [], []).
      apply bs_Assign.
      constructor. simpl in Heqs'. subst s'. apply st_binds_hd.
      apply bs_Write.
      constructor. apply st_binds_hd.
    }
    destruct H0.
    specialize (H2 H1).
    inversion H2.
    inversion H3.
    inversion STEP1.
    subst c'.
    inversion STEP2. 
    inversion STEP0.
    inversion VAL.
    inversion VAR.
    inversion H32.
  }
  exists ((Id 1 ::= Var (Id 2))).
  exists ((Id 2 ::= Var (Id 1))).
  split; assumption. 
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
    constructor; intros.
      -  inversion H.
        inversion STEP1.
        remember (bs_Seq c'1 c'0 c' s2 s3 STEP3 STEP2).
        apply (bs_Seq c c'1 c' s1 (s2 ;; s3) STEP0 b).
      - inversion H. inversion STEP2.
        remember (bs_Seq c c'0 c'1 s1 s2 STEP1 STEP0).
        apply (bs_Seq c c'1 c' (s1 ;; s2) s3 b STEP3).  
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. constructor; intros.
    - inversion H. apply bs_If_True. 
      + assumption.
      + apply (bs_Seq (st, i, o) c'0 c' s (WHILE e DO s END) STEP WSTEP).
      + apply (bs_If_False).
        * assumption.
        * apply bs_Skip.
    - inversion H.
      + inversion STEP.
        remember (bs_While_True s0 i o c'1 c' e s CVAL STEP1 STEP2).
        assumption.
      + remember (bs_While_False s0 i o e s CVAL).
        inversion STEP. assumption.    
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof. 
    dependent induction EXE.
    - specialize (IHEXE2 e s st i o).
      assert (WHILE e DO s END = WHILE e DO s END). 
        {reflexivity. }
      assert ((st, i, o) ~= (st, i, o)). 
        { auto. }
      apply (IHEXE2 H H0).
    - assumption.    
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. constructor.
    - intros. destruct c'. destruct p.
      remember (while_false (Nat 1) (SKIP) s l0 l c H).
      inversion e.
    - intros. inversion H.
      + inversion CVAL.
      + inversion CVAL.  
  Qed.
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    split; intros.
    - dependent induction H.
      + eapply bs_While_True.
        * assumption.
        * destruct (EQ ((st, i, o)) c').
          apply (H1 H).
        * specialize (IHbs_int2 e s1 EQ). 
          apply IHbs_int2. reflexivity.
      + apply bs_While_False.
        assumption.
    - dependent induction H.
      + eapply bs_While_True.
        * assumption.
        * destruct (EQ ((st, i, o)) c').
          apply (H2 H).
        * specialize (IHbs_int2 e s2 EQ). 
          apply IHbs_int2. reflexivity.
      + apply bs_While_False.
        assumption.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
    destruct c'. destruct p. intuition. 
    remember (while_false (Nat 1) s s0 l0 l c H).
    inversion e.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  constructor; intros.
  - inversion H. econstructor. 
    + eassumption.
    + destruct (EQ c'0 c').
      specialize (H4 STEP2).
      assumption.
  - inversion H. econstructor.
    + eassumption.
    + destruct (EQ c'0 c').
      specialize (H5 STEP2).
      assumption.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof. 
  constructor; intros.
  - inversion H. econstructor. 
    + destruct (EQ c c'0).
      specialize (H4 STEP1).
      eassumption.
    + assumption.
  - inversion H. econstructor. 
    + destruct (EQ c c'0).
      specialize (H5 STEP1).
      eassumption.
    + assumption.
Qed.

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.
  constructor; intros.
  - inversion H.
    + constructor.
      * assumption.
      * assumption.
    + apply bs_If_False.
      * assumption.
      * destruct (EQ ((s0, i, o)) c').
        specialize (H5 STEP). assumption.
  - inversion H.
    + constructor.
        * assumption.
        * assumption.
      + apply bs_If_False.
        * assumption.
        * destruct (EQ ((s0, i, o)) c').
          specialize (H6 STEP). assumption.
Qed.

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. 
  constructor; intros.
  - inversion H.
    + apply bs_If_True.
      * assumption.
      * destruct (EQ ((s0, i, o)) c').
        specialize (H5 STEP). assumption.
    + apply bs_If_False.
      * assumption.
      * assumption.
  - inversion H.
    + apply bs_If_True.
      * assumption.
      * destruct (EQ ((s0, i, o)) c').
        specialize (H6 STEP). assumption.
    + apply bs_If_False.
      * assumption.
      * assumption.
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
  split. apply (eq_congruence_seq_r s s1 s2 EQ).
  split. apply (eq_congruence_seq_l s s1 s2 EQ).
  split. apply (eq_congruence_cond_else e s s1 s2 EQ).
  split. apply (eq_congruence_cond_then e s s1 s2 EQ).
  apply (eq_congruence_while e s1 s2 EQ).
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
Proof. revert EXEC1 EXEC2. revert c c1 c2. induction s; intros.
- inversion EXEC1. inversion EXEC2. subst c1. assumption.
- inversion EXEC1. inversion EXEC2.
  rewrite <- H2 in H6. 
  assert (s0 = s). {  injection H6. auto. }
  assert (o0 = o). {  injection H6. auto. }
  assert (i0 = i1). {  injection H6. auto. }
  rewrite -> H in VAL0.
  remember (eval_deterministic e s z z0 VAL VAL0). subst z0.
  subst i0. subst o. subst s. reflexivity.
- inversion EXEC1. inversion EXEC2. rewrite <- H1 in H4.
  assert (s0 = s). { injection H4. auto. }  
  assert (o0 = o). { injection H4. auto. }
  assert (i0 = i1). { injection H4. auto. }
  assert (z0 = z). { injection H4. auto. }
  subst s. subst o. subst i0. subst z0. reflexivity.
- inversion EXEC1. inversion EXEC2. rewrite <- H1 in H4.
  assert (s0 = s). { injection H4. auto. }  
  assert (o0 = o). { injection H4. auto. }
  assert (i0 = i). { injection H4. auto. }
  assert (z0 = z). { 
    subst s0. 
    apply (eval_deterministic e s z0 z VAL0 VAL).
  }
  subst s. subst o. subst i0. subst z0. reflexivity.
- inversion EXEC1. inversion EXEC2.
  specialize (IHs1 c c' c'0 STEP1 STEP0). subst c'0.
  apply (IHs2 c' c1 c2 STEP2 STEP3).
- inversion EXEC1.
  + inversion EXEC2.  
      * assert (s4 = s). { subst c. injection H8. auto. }
        assert (o0 = o). { subst c. injection H8. auto. }
        assert (i0 = i). { subst c. injection H8. auto. }
        subst s4. subst o0. subst i0. 
        apply (IHs1 ((s, i, o)) c1 c2 STEP STEP0).
      * assert (s4 = s). { subst c. injection H8. auto. }
        assert (o0 = o). { subst c. injection H8. auto. }
        assert (i0 = i). { subst c. injection H8. auto. }
        subst s4. subst o0. subst i0.
        remember (eval_deterministic e s Z.zero Z.one CVAL0 CVAL).
        discriminate.
  + inversion EXEC2.
      * assert (s4 = s). { subst c. injection H8. auto. }
        assert (o0 = o). { subst c. injection H8. auto. }
        assert (i0 = i). { subst c. injection H8. auto. }
        subst s4. subst o0. subst i0.
        remember (eval_deterministic e s Z.zero Z.one CVAL CVAL0).
        discriminate.
      * assert (s4 = s). { subst c. injection H8. auto. }
        assert (o0 = o). { subst c. injection H8. auto. }
        assert (i0 = i). { subst c. injection H8. auto. }
        subst s4. subst o0. subst i0. 
        apply (IHs2 ((s, i, o)) c1 c2 STEP STEP0).
- dependent induction EXEC1.
  apply (IHEXEC1_2 s) with (e := e).
  + assumption.
  + reflexivity.
  + inversion EXEC2.
    * specialize (IHs ((st, i, o)) c'0 c' STEP EXEC1_1).
      subst c'0. assumption.
    * remember (eval_deterministic e st Z.zero Z.one CVAL0 CVAL).
      discriminate.
  + symmetry.
    inversion EXEC2.
    * remember (eval_deterministic e st Z.zero Z.one CVAL CVAL0).
      discriminate.
    * reflexivity.
Qed.

(* Contextual equivalence is equivalent to the semantic one *)
(* TODO: no longer needed *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); assumption.

  
(* Lemma bs_eq_eq_ceq.
*)

Lemma bs_eq_stronger s1 s2: s1 ~~~ s2 -> s1 ~e~ s2.
Proof.
  unfold eval_equivalent. intros.
  split; intros; unfold eval in *;
  destruct H0 as [st H0]; exists st;
  apply H; assumption.  
Qed.

Lemma eq_eq_ceq s1 s2: s1 ~~~ s2 -> s1 ~c~ s2.
Proof.
  intros.
  - unfold contextual_equivalent.
    intros C. apply bs_eq_stronger. 
    generalize dependent C.
    induction C.
    + simpl. apply H.
    + simpl. intros.
      apply eq_congruence_seq_l. assumption.
    + simpl. apply eq_congruence_seq_r. assumption.
    + simpl. apply eq_congruence_cond_then. assumption.
    + simpl. apply eq_congruence_cond_else. assumption.
    + simpl. apply eq_congruence_while. assumption.
Qed.

(*
The s1 ~c~ s2 -> s1 ~~~ s2 is false
  - admit.
Admitted. 

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
  Proof.
    revert EXEC1 EXEC2. revert c c' c''. induction s; intros.
    - inversion EXEC1. inversion EXEC2. reflexivity.
    - inversion EXEC1. inversion EXEC2.
      assert (s0 = s). {subst c. injection H6. auto. }
      subst s0.
      assert (z0 = z). { 
        apply (eval_deterministic e s). 
        assumption. assumption.
      } subst z0. 
      assert (i0 = i1). {subst c. injection H6. auto. } 
      subst i0.
      assert (o0 = o). {subst c. injection H6. auto. }
      subst o0. reflexivity.
    - inversion EXEC1. inversion EXEC2.
      assert (s0 = s). {subst c. injection H4. auto. }
      subst s0.
      assert (z0 = z). {
        subst c. injection H4. auto. 
      } subst z0. 
      assert (i0 = i1). {subst c. injection H4. auto. } 
      subst i0.
      assert (o0 = o). {subst c. injection H4. auto. }
      subst o0. reflexivity.
    - inversion EXEC1. inversion EXEC2.
      assert (s0 = s). {subst c. injection H4. auto. }
      subst s0.
      assert (z0 = z). { 
        apply (eval_deterministic e s). 
        assumption. assumption.
      } subst z0. 
      assert (i0 = i). {subst c. injection H4. auto. } 
      subst i0.
      assert (o0 = o). {subst c. injection H4. auto. }
      subst o0. reflexivity.
    - inversion EXEC1.
      + inversion EXEC2;
        remember (IHs1 c _ _ SSTEP0 SSTEP).
        * injection e. intros. subst c'0. reflexivity.
        * discriminate e.
      + inversion EXEC2; remember (IHs1 c _ _ SSTEP0 SSTEP).
        * discriminate e.
        * injection e. intros. subst s1'. subst c'0. reflexivity.
    - inversion EXEC1.
      + inversion EXEC2; subst c; injection H8; intros.
        * subst o. subst i. subst s. reflexivity.
        * subst s4. discriminate (eval_deterministic e s Z.one Z.zero SCVAL SCVAL0).
      + inversion EXEC2; subst c; injection H8; intros.
        * subst s4. discriminate (eval_deterministic e s Z.one Z.zero SCVAL0 SCVAL).
        * subst o. subst i. subst s. reflexivity.
    - dependent induction EXEC1. inversion EXEC2.
      reflexivity.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
    induction STEP1. 
    - inversion STEP2. 
      + injection (ss_int_step_deterministic s c ((None, c')) ((None, c''))). 
        auto. assumption. assumption.
      + discriminate (ss_int_step_deterministic s c ((None, c')) ((Some s', c'0))).
        assumption. assumption.
    - inversion STEP2.
      + discriminate (ss_int_step_deterministic s c ((None, c'')) ((Some s', c'))).
        assumption. assumption.
      + remember (ss_int_step_deterministic s c ((Some s', c')) ((Some s'0, c'0)) H H0).
        injection e. intros. subst s'0. subst c'0.
        apply IHSTEP1. assumption.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
    inversion STEP.
    - apply bs_Skip.
    - apply bs_Assign. assumption.
    - apply bs_Read.
    - apply bs_Write. assumption.
  Qed.   

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof. 
    induction STEP1.
    - eapply ss_int_Step.
      eapply ss_Seq_Compl.
      eassumption.
      assumption.
    - eapply ss_int_Step.
      eapply ss_Seq_InCompl.
      eassumption.
      apply IHSTEP1.
      assumption.
  Qed.
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    revert EXEC STEP. revert s' c c' c''. induction s; intros.
    - inversion STEP.
    - inversion STEP.
    - inversion STEP.
    - inversion STEP.
    - inversion STEP.
      + remember (ss_bs_base s1 c c' SSTEP).
        eapply bs_Seq. eassumption. assumption.
      + subst s'. inversion EXEC.
        specialize (IHs1 s1' c c' c'1 STEP1 SSTEP).
        eapply bs_Seq. eassumption. eassumption.
    - inversion STEP.
      + apply bs_If_True. assumption.
        subst c'. assumption.
      + apply bs_If_False. assumption.
        subst c'. assumption.
    - dependent induction STEP.
      inversion EXEC. 
      + inversion STEP. 
        apply bs_While_True with (c' := c'1).
        assumption.
        assumption.
        assumption.
      + inversion STEP.
        apply bs_While_False.
        assumption.
  Qed.
        
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. 
    split.
    - intros. induction  H.
      + apply ss_int_Base. apply ss_Skip.
      + apply ss_int_Base. apply ss_Assign. assumption.
      + apply ss_int_Base. apply ss_Read.
      + apply ss_int_Base. apply ss_Write. assumption.
      + eapply ss_ss_composition. eassumption. assumption.
      + eapply ss_int_Step.
        * apply ss_If_True. assumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_If_False. assumption.
        * assumption.
      + eapply ss_int_Step.
        * apply ss_While.
        * eapply ss_int_Step.
          ++ apply ss_If_True. assumption.
          ++ inversion H0.
            ** eapply ss_ss_composition. eassumption. assumption.
            ** eapply ss_ss_composition. eassumption. subst c''. assumption.
      + eapply ss_int_Step.
        * eapply ss_While.
        * eapply ss_int_Step.
          ++ apply ss_If_False. assumption.
          ++ apply ss_int_Base. apply ss_Skip.
    - intros. induction H.
      + apply ss_bs_base. assumption.
      + eapply ss_bs_step. eassumption. assumption.
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
    induction s.
    - reflexivity.
    - simpl. remember (Hinv i). 
      rewrite e0. 
      specialize (Renaming.re_rename_expr r r' Hinv e) as H.
      rewrite H. reflexivity.
    - simpl. specialize (Hinv i). rewrite Hinv. reflexivity.
    - simpl. specialize (Renaming.re_rename_expr r r' Hinv e) as H.
      rewrite H. reflexivity.
    - simpl. rewrite IHs1. rewrite IHs2. reflexivity.
    - simpl. specialize (Renaming.re_rename_expr r r' Hinv e) as H.
      rewrite H. rewrite IHs1. rewrite IHs2. reflexivity.
    - simpl. specialize (Renaming.re_rename_expr r r' Hinv e) as H.
      rewrite H. rewrite IHs. reflexivity.
  Qed.    

  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    simpl. unfold Renaming.rename_id.
    destruct r eqn:R. rewrite <- R.
    reflexivity. 
  Qed.

  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  (** ADDITIONAL LEMMAS (Some of them were added to task, TODO: deduplicate)**)

  Lemma renaming_state_injection (st st' : state Z) (r : renaming) : 
    st = st' <-> Renaming.rename_state r st = Renaming.rename_state r st'.
  Proof.
    split. 
    - intros. subst st. reflexivity. 
    - revert st'. induction st; intros.
      + simpl in H.
        destruct st'.
        * reflexivity.
        * simpl in H. destruct r. destruct p. discriminate.
      + simpl in H. destruct r eqn:R. 
        rewrite <- R in H. rewrite <- R in IHst. destruct a.
        destruct st'.
        * simpl in H. discriminate.
        * destruct p. simpl in H. destruct r eqn:R'.
          simpl in H. rewrite <- R' in H. rewrite <- R' in IHst.
          injection H. intros. specialize (IHst st' H0).
          subst st'. injection R. intros. subst x0.
          specialize (Renaming.bijective_injective x b) as I.
          unfold FinFun.Injective in I.
          specialize (I i i0 H2). subst i0. subst z0.
          reflexivity.
  Qed.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct c as [[st i] o].
    destruct c' as [[st' i'] o'].
    simpl.
    rename Hbs into H.
    generalize dependent st.
    generalize dependent st'. 
    generalize dependent o.
    generalize dependent o'.
    generalize dependent i.
    generalize dependent i'.
    induction s; intros.
    - intros. simpl.
      + destruct r eqn:R.
        inversion H.
        apply bs_Skip.
    - intros. simpl.
      + inversion H. simpl. destruct r eqn:R. simpl.
        rewrite <- R. 
        apply bs_Assign.
        apply Renaming.eval_renaming_invariance.
        assumption.
    - intros. simpl.
      + inversion H. inversion H. simpl.
        destruct r eqn:R. simpl. rewrite <- R.
        apply bs_Read.
    - intros. simpl.
      + inversion H. destruct r eqn:R. apply bs_Write.
        apply (Renaming.eval_renaming_invariance). 
        assumption.
    - intros. simpl.
      + inversion H.
        destruct r eqn:R. simpl.
        rewrite <- R. rewrite <- R in IHs1.
        rewrite <- R in IHs2.
        destruct c'. destruct p.
        eapply bs_Seq.
        apply IHs1. eassumption.
        apply IHs2. assumption.
    - intros. simpl.
      + inversion H.
        * destruct r eqn:R. rewrite <- R.
          apply bs_If_True. apply Renaming.eval_renaming_invariance.
          assumption. rewrite <- R in IHs1. apply IHs1.
          assumption.
        * destruct r eqn:R. rewrite <- R. 
          apply bs_If_False. apply Renaming.eval_renaming_invariance.
          assumption. rewrite <- R in IHs2. apply IHs2.
          assumption.
    - intros. simpl.
      + destruct r eqn:R. rewrite <- R.
        rewrite <- R in IHs.
        dependent induction H.
        * remember (exist (fun f : id -> id => FinFun.Bijective f) x b) as r eqn:R. 
          destruct c'. destruct p.
          eapply bs_While_True.
          -- apply Renaming.eval_renaming_invariance.
             assumption.
          -- apply IHs. eassumption.
          -- eapply IHbs_int2. 
             eassumption.
             eassumption.
             reflexivity.
             reflexivity.
             reflexivity.
        * remember (exist (fun f : id -> id => FinFun.Bijective f) x b) as r eqn:R.
          apply bs_While_False. apply Renaming.eval_renaming_invariance.
          assumption.
  Qed.  

  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    specialize (Renaming.renaming_inv r) as H.
    destruct H as [r' H].
    specialize (renaming_invariant_bs (rename r s) r' (rename_conf r c) (rename_conf r c') Hbs) as R.
    destruct c as [[st i] o].
    destruct c' as [[st' i'] o'].
    unfold rename_conf in R. 
    rewrite Renaming.re_rename_state in R.
    rewrite Renaming.re_rename_state in R. 
    rewrite re_rename in R.
    all: assumption.
  Qed.

  Lemma renaming_inversible (st : state Z) (r : renaming):
    exists (st' : state Z), st = Renaming.rename_state r st'. 
  Proof.
    induction st.
    - exists ([]). reflexivity.
    - destruct r as [f b] eqn:R. 
      rewrite <- R. rewrite <- R in IHst.
      inversion b as [g I].
      destruct IHst.
      destruct a.
      exists ((g i, z) :: x). simpl. rewrite -> R.
      simpl. rewrite <- R. subst st.
      destruct I. specialize (H0 i).
      rewrite H0.
      reflexivity.  
  Qed.


  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    constructor; intros.
    - inversion H.
      exists (Renaming.rename_state r x).
      specialize (renaming_invariant_bs s r (([], i, []))  ((x, [], o)) H0) as R. 
      assumption.
    - inversion H.
      destruct (renaming_inversible x r). subst x.
      assert ((Renaming.rename_state r ([])) = ([])). 
      {
        reflexivity.
      }
      rewrite <- H1 in H0.
      econstructor. apply renaming_invariant_bs_inv with r.
      eassumption.
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
induction EXEC; intros; try discriminate. 
- destruct k; try discriminate; inversion DEF.
  + inversion EXEC. apply bs_Skip.
  + apply bs_Seq with c. apply bs_Skip.
    apply IHEXEC. reflexivity.
- destruct k; try discriminate; inversion DEF.
  + inversion EXEC. apply bs_Assign. assumption.
  + eapply bs_Seq. apply bs_Assign. 
    eassumption. apply IHEXEC. reflexivity.
- destruct k; try discriminate; inversion DEF.
  + inversion EXEC. apply bs_Read.
  + eapply bs_Seq. apply bs_Read. apply IHEXEC.
    reflexivity.
- destruct k; try discriminate; inversion DEF.
  + inversion EXEC. apply bs_Write. assumption.
  + eapply bs_Seq. apply bs_Write. eassumption.
    apply IHEXEC. reflexivity.
- destruct k; try discriminate; inversion DEF.
  + apply IHEXEC. reflexivity.
  + assert (forall s1' s2' s3' c c', c == s1';;(s2';;s3') ==> c' -> 
  c == (s1';;s2');;s3' ==> c'). {
     intros. inversion H.
     inversion STEP2.
     eapply bs_Seq.
     eapply bs_Seq.
     all: eassumption. 
  } apply SmokeTest.seq_assoc.
  apply IHEXEC. reflexivity.
- destruct k. inversion DEF.
  + apply bs_If_True. assumption.
    apply IHEXEC. reflexivity.
  + assert (forall s1' s2' s3' c' e' s' i' o' , 
      [|e'|] s' => (Z.one) -> (((s', i', o')) == s1' ;; s3' ==> c' -> 
      ((s', i' , o')) == (COND e' THEN s1' ELSE s2' END) ;; s3' ==> c')). {
        intros. 
        inversion H0.
        apply bs_Seq with c'1. apply bs_If_True.
        assumption. assumption. assumption.
      }
      inversion DEF. eapply H. eassumption. apply IHEXEC.
      reflexivity.
- destruct k; inversion DEF.
  + apply bs_If_False. assumption.
    apply IHEXEC. reflexivity.
  + assert (forall s1' s2' s3' c' e' s' i' o' , 
      [|e'|] s' => (Z.zero) -> (((s', i', o')) == s2' ;; s3' ==> c' -> 
      ((s', i' , o')) == (COND e' THEN s1' ELSE s2' END) ;; s3' ==> c')). {
        intros. 
        inversion H1.
        apply bs_Seq with c'1. apply bs_If_False.
        assumption. assumption. assumption.
      }
      eapply H. eassumption. apply IHEXEC.
      reflexivity.
- destruct k. 
  + specialize (SmokeTest.while_unfolds e s) as WU.
    inversion DEF. apply WU. 
    apply bs_If_True. assumption. apply IHEXEC.
    reflexivity.
  + assert (forall s1' s2' c' e' s' i' o' , 
    [|e'|] s' => (Z.one) -> (((s', i', o')) == s1' ;; (WHILE e' DO s1' END) ;; s2' ==> c' -> 
    ((s', i' , o')) == (WHILE e' DO s1' END) ;; s2' ==> c')). {
    intros. 
    inversion H0. inversion STEP2.
    eapply bs_Seq. eapply bs_While_True.
    assumption. eassumption. eassumption. eassumption.
    } specialize (SmokeTest.while_unfolds e s) as WU.
    inversion DEF. apply H. assumption.
    apply IHEXEC. reflexivity.
- destruct k.
  + inversion EXEC. inversion DEF. apply bs_While_False.
    assumption.
  + assert (forall s1' s2' c' e' s' i' o' , 
      [|e'|] s' => (Z.zero) -> (((s', i', o')) == s2' ==> c' -> 
     ((s', i' , o')) == (WHILE e' DO s1' END) ;; s2' ==> c')). {
        intros. eapply bs_Seq. apply bs_While_False.
        assumption. assumption.
     }
    inversion DEF. apply H. assumption.
    apply IHEXEC. reflexivity. 
Qed.


Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. 
  eapply cps_bs_gen. eassumption.
  reflexivity.
Qed. 

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof.
  eapply cps_bs_gen. eassumption.
  reflexivity.
Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof.
  destruct k1.
  - destruct k2.
    + unfold Kapp in *. assumption.
    + destruct k3.
      * unfold Kapp in *.
        inversion STEP.
      * unfold Kapp in *. 
        inversion STEP.
  - destruct k2. 
    + unfold Kapp in *.
      assumption.
    + destruct k3. 
      * unfold Kapp in *.
        apply cps_Seq. unfold Kapp. assumption.
      * apply cps_Seq. assumption.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof.
  generalize dependent k.
  induction EXEC; intros.
  - assumption.
  - apply cps_Assign with z. assumption.
    inversion STEP. assumption.
  - apply cps_Read. inversion STEP. assumption.
  - apply cps_Write with z. assumption.
    inversion STEP. assumption.
  - apply cps_Seq. apply IHEXEC1.
    destruct k; unfold Kapp.
    + apply cps_Skip. apply IHEXEC2. assumption.
    + apply cps_Skip. apply cps_Seq.
      unfold Kapp. apply IHEXEC2. assumption.
  - apply cps_If_True. assumption.
    apply IHEXEC. assumption.
  - apply cps_If_False. assumption.
    apply IHEXEC. assumption.
  - apply cps_While_True. assumption.
    destruct k; unfold Kapp.
    + apply IHEXEC1. apply cps_Skip. 
      apply IHEXEC2. assumption.
    + apply IHEXEC1. apply cps_Skip.
      apply cps_Seq. unfold Kapp.
      apply IHEXEC2. assumption.
  - apply cps_While_False. assumption.
    inversion STEP. assumption.
Qed.
     
Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof.
  eapply bs_int_to_cps_int_cont.
  eassumption. apply cps_Skip.
  apply cps_Empty.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
