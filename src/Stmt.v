Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.
Require Import Coq.Program.Equality.

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
Proof. specialize (H Hole). apply H. Qed. 

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof. 
  assert (WRITE ( (Nat 8) [-] Var (Id 0) )) ~e~ (WRITE (Var (Id 0) [-] (Nat 8))).
    intro. intro. split.
      + intro. inversion H. inversion H0. subst. inversion VAL. inversion VALB. inversion VAR.
      + intro. inversion H. inversion H0. subst. inversion VAL. inversion VALA. inversion VAR.
  + exists (WRITE ( (Nat 8) [-] Var (Id 0) )). exists (WRITE (Var (Id 0) [-] (Nat 8))).
    split.
      - apply H.
      - intro. specialize (H0 (SeqR (Assn (Id 0) (Nat 3)) (Hole)) nil ([5%Z])).
          unfold eval_equivalent in H0. unfold plug in H0. unfold eval in H0.
          destruct H0. destruct H0. exists [((Id 0), 3%Z)].
          econstructor. apply bs_Assign. apply bs_Nat.
          econstructor.
          assert ((8 - 3)%Z = 5%Z).
            simpl. reflexivity. 
          rewrite <- H0. apply bs_Sub. apply bs_Nat.
          apply bs_Var. apply st_binds_hd.
          inversion H0. subst. 
          inversion STEP1. subst. 
          inversion STEP2. subst.
          inversion VAL. subst.
          inversion STEP1. subst.
          inversion VAL0. subst.
          inversion VALB. subst.
          inversion VALA. subst.
          inversion VAR. subst. 
          inversion H6. apply H8.
          reflexivity. 
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
  Proof. intro. intro. split. intro. inversion H. subst.
    inversion STEP1. subst. apply bs_Seq with c'1. exact STEP0. apply bs_Seq with c'0. exact STEP3. exact STEP2.
    intro. inversion H. subst. inversion STEP2. apply bs_Seq with c'1. apply bs_Seq with c'0. exact STEP1. exact STEP0. exact STEP3. Qed.
  
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
  Proof. dependent induction EXE. 
    + specialize (IHEXE2 e s st i o ). apply IHEXE2. reflexivity. reflexivity.
    + auto.
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. unfold bs_equivalent. intro. intro. split.
    + intro. dependent induction H.
      - inversion H. rewrite H3. apply IHbs_int2. reflexivity.
      - inversion CVAL.
    + intro. dependent induction H.
      - inversion CVAL.
      - inversion CVAL.
  Qed.
  
  Lemma conf_equivalent : forall (s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf),
     (c1 == s1 ==> c2) -> (c1 == s2 ==> c2)).
  Proof. intros. 
    destruct H with c1 c2. auto. 
  Qed.
  
  Lemma while_conf_equivalent : forall (e: expr) (s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf),
     (c1 == WHILE e DO s1 END ==> c2) -> (c1 == WHILE e DO s2 END ==> c2)).
  Proof. intros. dependent induction H0.
    + apply (conf_equivalent s1 s2) in H0_.
      - econstructor. auto. eauto.
         specialize IHbs_int2 with e s1.
         apply IHbs_int2. auto. auto.
      - apply H.
    + apply bs_While_False. auto.
  Qed. 

  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof. unfold bs_equivalent. intro. intro. split.
    + intro. apply while_conf_equivalent with s1. apply EQ. apply H.
    + intro. apply while_conf_equivalent with s2. apply bs_equiv_symm. apply EQ. apply H.
  Qed.
  
  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof. intro. dependent induction H.
    + apply IHbs_int2 with s. auto.
    + inversion CVAL.
  Qed.
  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof. intro. intro. split. intro. dependent induction H.
  + econstructor. apply H. apply SmokeTest.conf_equivalent with (s2:=s2) in H0.
    auto. auto.
  + intro. dependent induction H. econstructor.
    - eauto.
    - apply SmokeTest.conf_equivalent with (s2:=s1) in H0. auto. apply bs_equiv_symm. auto.
Qed.

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof. intro. intro. split. intro. dependent induction H.
  + econstructor. apply SmokeTest.conf_equivalent with (s2:=s2) in H.
    apply H. apply EQ. apply H0.
  + intro. dependent induction H. econstructor.
    - apply SmokeTest.conf_equivalent with (s2:=s1) in H.
      apply H. apply bs_equiv_symm. apply EQ.
    - apply H0.
Qed.

Lemma cond_else_conf_equivalent : forall (e: expr) (s s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf),
    (c1) == COND e THEN s ELSE s1 END ==> (c2) -> (c1) == COND e THEN s ELSE s2 END ==> (c2)).
Proof. intros. dependent induction H0.
  + apply bs_If_True. auto. auto. 
  + apply bs_If_False. auto. apply SmokeTest.conf_equivalent with (s2:=s2) in H0.
    auto. auto.
Qed. 

Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof. unfold bs_equivalent. intros. split.
  + apply cond_else_conf_equivalent. auto. 
  + apply cond_else_conf_equivalent. apply bs_equiv_symm. auto.
Qed. 

Lemma cond_then_conf_equivalent : forall (e: expr) (s s1 s2 : stmt), (s1 ~~~ s2) -> (forall (c1 c2 : conf),
    (c1) ==  COND e THEN s1 ELSE s END ==> (c2) -> (c1) == COND e THEN s2 ELSE s END ==> (c2)).
Proof. intros. dependent induction H0.
  + apply bs_If_True. apply CVAL. apply SmokeTest.conf_equivalent with (s2:=s2) in H0. 
    auto. auto.
  + apply bs_If_False. auto. auto.
Qed. 

Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof. unfold bs_equivalent. intro. intro. split.
  + apply cond_then_conf_equivalent. auto.
  + apply cond_then_conf_equivalent. apply bs_equiv_symm. auto.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. apply SmokeTest.while_eq. auto. Qed.

Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof. split. 
  + apply eq_congruence_seq_r. auto.
  + split.
    - apply eq_congruence_seq_l. auto.
    - split.
      * apply eq_congruence_cond_else. auto.
      * split.
        ++ apply eq_congruence_cond_then. auto.
        ++ apply eq_congruence_while. auto.
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
Proof. generalize dependent c2. induction EXEC1.
  all: intros.
  all: inversion EXEC2.
  all: try reflexivity.
  all: try by_eval_deterministic.
  all: try eval_zero_not_one.
  all: try apply IHEXEC1.
  all: try apply STEP.
  all: try apply IHEXEC1_1 in STEP1.
  all: try apply IHEXEC1_1 in STEP.
  all: try apply IHEXEC1_2.
  all: subst.
  all: try apply STEP2.
  all: try apply WSTEP.
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
  Proof. generalize dependent c''. induction EXEC1.
    all: intros.
    all: inversion EXEC2.
    all: try by_eval_deterministic.
    all: try eval_zero_not_one.
    all: try apply IHEXEC1 in SSTEP.
    all: try inversion SSTEP.
    all: subst.
    all: try reflexivity.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof. generalize dependent c''. induction STEP1.
    + intro. intro. inversion STEP2.
      - subst. apply (ss_int_step_deterministic s c (None, c'')) in H. inversion H. auto. auto.
      - subst. apply (ss_int_step_deterministic s c(Some s', c'0)) in H. inversion H. auto.
    + intro. intro. inversion STEP2.
      - subst. apply (ss_int_step_deterministic s c (Some s', c')) in H0. inversion H0. auto.
      - subst. apply (ss_int_step_deterministic s c (Some s'0, c'0)) in H. inversion H. subst.
        apply IHSTEP1 in H1. auto. auto.
  Qed.
  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof. inversion STEP.
    all: econstructor; auto.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof. generalize dependent c'. induction STEP1.
    + intros. eapply ss_int_Step.
      - econstructor. eauto.
      - auto.
    + intros. apply IHSTEP1 in STEP2. apply (ss_int_Step (s;; s2) (s';; s2) c) in STEP2.
      - apply STEP2.
      - econstructor. auto.
  Qed.

  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof. admit. Admitted.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof. split.
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
  Proof. induction s.
    + auto.
    + simpl. rewrite Hinv. rewrite Renaming.re_rename_expr. auto. auto.
    + simpl. rewrite Hinv. auto.
    + simpl. rewrite Renaming.re_rename_expr. auto. auto.
    + simpl. rewrite IHs1. rewrite IHs2. auto. 
    + simpl. rewrite Renaming.re_rename_expr.
      - rewrite IHs1. rewrite IHs2. auto.
      - auto.
    + simpl. rewrite Renaming.re_rename_expr.
      - rewrite IHs. auto.
      - auto.
    Qed. 
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof. induction st.
    + destruct r. reflexivity.
    + destruct r. reflexivity.
  Qed.
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof. destruct r. induction Hbs.
    + econstructor.
    + econstructor. apply Renaming.eval_renaming_invariance. auto.
    + econstructor.
    + econstructor. apply Renaming.eval_renaming_invariance. auto.
    + econstructor. eauto. eauto. 
    + econstructor. apply Renaming.eval_renaming_invariance. auto. auto.
    + apply bs_If_False. apply Renaming.eval_renaming_invariance. auto. auto.
    + econstructor. apply Renaming.eval_renaming_invariance. auto. eauto. eauto.
    + apply bs_While_False. apply Renaming.eval_renaming_invariance. auto.
  Qed.
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof. intros. 
    specialize (Renaming.renaming_inv r). intros.
    destruct H.
    apply renaming_invariant_bs with (r:=x) in Hbs.  
    rewrite re_rename in Hbs.
      + destruct c', c. destruct p0, p. unfold rename_conf in Hbs.
        rewrite Renaming.re_rename_state in Hbs. rewrite Renaming.re_rename_state in Hbs.
        auto. auto. auto.
      + auto.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof. split.
    + intro. destruct H. apply renaming_invariant_bs with (r:=r) in H.
        unfold rename_conf in H. simpl in H.
        exists (Renaming.rename_state r x). apply H.
    + intro. destruct H.
      assert (rename_conf r ([], i, []) = ([], i, [])).
        unfold rename_conf. simpl. reflexivity.
      destruct (Renaming.renaming_inv2 r).
      assert (rename_conf r ((Renaming.rename_state x0 x), [], o) = (x, [], o)).
        unfold rename_conf. rewrite Renaming.re_rename_state.
        reflexivity. apply H1.
      rewrite <- H2 in H. rewrite <- H0 in H.
      apply renaming_invariant_bs_inv in H.
      exists (Renaming.rename_state x0 x). apply H.
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
Proof. admit. Admitted.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. apply (cps_bs_gen (s1 ;; s2)) in STEP. auto. auto. Qed.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. apply (cps_bs_gen s) in STEP. auto. auto. Qed.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. destruct k1, k2.
  + inversion STEP. unfold Kapp in H. subst. apply cps_Empty.
  + inversion STEP. destruct k3. inversion H0. inversion H0.
  + inversion STEP; destruct k3; subst; unfold Kapp; eauto.
  + inversion STEP; destruct k3; subst; unfold Kapp; apply cps_Seq; eauto.
Qed.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. generalize dependent k. induction EXEC.
  all: intros.
  1-4: auto; econstructor; try apply VAL; inversion STEP; apply CSTEP.
  - econstructor. eapply IHEXEC1. econstructor. destruct k.
    * auto.
    * econstructor. auto.
  - econstructor. destruct k. auto. auto. auto.
  - apply cps_If_False. auto. auto. 
  - econstructor. auto. eapply IHEXEC1. destruct k. 
    all: do 3 (auto; econstructor).
  - apply cps_While_False. auto. inversion STEP. destruct k. auto. auto.
Qed.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. dependent induction EXEC.
  1-4: do 2 (eauto; econstructor).
  + econstructor; eapply bs_int_to_cps_int_cont; eauto. 
    econstructor; eapply bs_int_to_cps_int_cont; eauto. 
    econstructor. econstructor.
  + econstructor. auto. auto. 
  + apply cps_If_False. auto. auto.
  + econstructor. auto. eapply bs_int_to_cps_int_cont. eauto.
    econstructor. eapply bs_int_to_cps_int_cont. eauto.
    econstructor. econstructor.
  + apply cps_While_False. auto. econstructor.
Qed.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
