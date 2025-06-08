Set Warnings "-notation-overridden,-non-recursive,-implicit-core-hint-db".

Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

Require Import Coq.Program.Equality.
Require Import List.
Import ListNotations.

From hahn Require Import HahnBase.

(* Type of binary operators *)
Inductive bop : Type :=
| Add : bop
| Sub : bop
| Mul : bop
| Div : bop
| Mod : bop
| Le  : bop
| Lt  : bop
| Ge  : bop
| Gt  : bop
| Eq  : bop
| Ne  : bop
| And : bop
| Or  : bop.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
| Nat : Z -> expr
| Var : id  -> expr              
| Bop : bop -> expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Bop Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Bop Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Bop Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Bop Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Bop Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Bop Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Bop Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Bop Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Bop Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Bop Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Bop Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (Bop And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Bop Or  x y) (at level 38, left associativity).

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.
  
Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.one else Z.zero.

Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

Inductive eval : expr -> state Z -> Z -> Prop := 
  bs_Nat  : forall (s : state Z) (n : Z), [| Nat n |] s => n

| bs_Var  : forall (s : state Z) (i : id) (z : Z) (VAR : s / i => z),
    [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb),
    [| a [+] b |] s => (za + zb)

| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb),
    [| a [-] b |] s => (za - zb)

| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb),
    [| a [*] b |] s => (za * zb)

| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (NZERO : ~ zb = Z.zero),
    [| a [/] b |] s => (Z.div za zb)

| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (NZERO : ~ zb = Z.zero),
    [| a [%] b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.le za zb),
    [| a [<=] b |] s => Z.one

| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z) 
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.gt za zb),
    [| a [<=] b |] s => Z.zero

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.lt za zb),
    [| a [<] b |] s => Z.one

| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.ge za zb),
    [| a [<] b |] s => Z.zero

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.ge za zb),
    [| a [>=] b |] s => Z.one

| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.lt za zb),
    [| a [>=] b |] s => Z.zero

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.gt za zb),
    [| a [>] b |] s => Z.one

| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.le za zb),
    [| a [>] b |] s => Z.zero
                         
| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.eq za zb),
    [| a [==] b |] s => Z.one

| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : ~ Z.eq za zb),
    [| a [==] b |] s => Z.zero

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : ~ Z.eq za zb),
    [| a [/=] b |] s => Z.one

| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (OP : Z.eq za zb),
    [| a [/=] b |] s => Z.zero

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (BOOLA : zbool za)
                   (BOOLB : zbool zb),
    [| a [&] b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z)
                   (VALA : [| a |] s => za)
                   (VALB : [| b |] s => zb)
                   (BOOLA : zbool za)
                   (BOOLB : zbool zb),
    [| a [\/] b |] s => (zor za zb)
where "[| e |] st => z" := (eval e st z). 

#[export] Hint Constructors eval : core.

Module SmokeTest.

  Lemma zero_always x (s : state Z) (n : Z) (H: s / x => n) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof.
    assert ((n * 0)%Z = Z.zero) as H0 by (apply Zmult_0_r).
    rewrite <- H0.
    apply bs_Mul with (za := n) (zb := Z.zero).
    - apply bs_Var. exact H.
    - apply bs_Nat.
  Qed.
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. 
    apply bs_Nat.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH; subst.
    inversion VALB; subst.
    rewrite <- Zplus_diag_eq_mult_2.
    apply bs_Add; assumption.
  Qed.
  
End SmokeTest.

Reserved Notation "e1 << e2" (at level 0).

Inductive subexpr : expr -> expr -> Prop :=
  subexpr_refl : forall e : expr, e << e
| subexpr_left : forall e e' e'' : expr, forall op : bop, e << e' -> e << (Bop op e' e'')
| subexpr_right : forall e e' e'' : expr, forall op : bop, e << e'' -> e << (Bop op e' e'')
where "e1 << e2" := (subexpr e1 e2).

Lemma strictness (e e' : expr) (HSub : e' << e) (st : state Z) (z : Z) (HV : [| e |] st => z) :
  exists z' : Z, [| e' |] st => z'.
Proof.
  generalize dependent z.
  generalize dependent st.
  induction HSub; intros.
  - exists z. exact HV.
  - inversion HV; subst; 
    apply IHHSub with za; assumption.
  - inversion HV; subst;
    apply IHHSub with zb; assumption.
Qed.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (a b : expr) (op : bop), id ? a \/ id ? b -> id ? (Bop op a b)
where "x ? e" := (V e x).

#[export] Hint Constructors V : core.

(* If an expression is defined in some state, then each its' variable is
   defined in that state
 *)      
Lemma defined_expression
      (e : expr) (s : state Z) (z : Z) (id : id)
      (RED : [| e |] s => z)
      (ID  : id ? e) :
  exists z', s / id => z'.
Proof.
  generalize dependent z.
  induction e.
  - intros z' RED. inversion RED. subst. inversion ID.
  - intros z' RED. inversion RED. subst. inversion ID. subst. exists z'. assumption.
  - intros z' RED. inversion RED. subst. 
    all: (inversion_clear ID; destruct H). 
    all: try (apply IHe1 with (z:=za) in H; assumption; assumption).
    all: try (apply IHe2 with (z:=zb) in H; assumption; assumption).
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z H_eval.
  (* If expression evaluates, then all its variables must be defined *)
  destruct (defined_expression e s z id H_eval ID) as [z' H_id_defined].
  (* But we know id is undefined - contradiction *)
  exact (UNDEF z' H_id_defined).
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. 
  generalize dependent z2. generalize dependent z1.
  induction e; intros z1 H_eval1 z2 H_eval2.
  - inversion H_eval1; inversion H_eval2; subst; reflexivity.
  - inversion H_eval1; inversion H_eval2; subst.
    eapply state_deterministic; eassumption.
  - inversion H_eval1; subst; inversion H_eval2; subst;
    specialize IHe1 with (z1:=za) (z2:=za0);
    specialize IHe2 with (z1:=zb) (z2:=zb0); 
    intuition;
    try (subst; reflexivity);
    try (rewrite H1 in OP; rewrite H in OP; contradiction).
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof. 
  generalize dependent z.
  induction e; intros z0 H_eval.
  - inversion H_eval; subst; constructor.
  - inversion H_eval; subst.
    apply FV in VAR.
    + constructor; assumption.
    + constructor.
  - inversion H_eval; subst; econstructor; eauto.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. 
  unfold equivalent. intros. reflexivity.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. 
  unfold equivalent. unfold equivalent in EQ. intros. specialize (EQ n s). symmetry. assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. unfold equivalent in *. intros n s. transitivity ([|e2|] s => n); auto. Qed.

Inductive Context : Type :=
| Hole : Context
| BopL : bop -> Context -> expr -> Context
| BopR : bop -> expr -> Context -> Context.

Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | BopL b C e1 => Bop b (plug C e) e1
  | BopR b e1 C => Bop b e1 (plug C e)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

Definition contextual_equivalent (e1 e2 : expr) : Prop :=
  forall (C : Context), (C <~ e1) ~~ (C <~ e2).

Notation "e1 '~c~' e2" := (contextual_equivalent e1 e2)
                            (at level 42, no associativity).

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof. 
  split.
  - intros H_equiv. split; intros; generalize dependent n; induction C; intros.
    + apply H_equiv in H. assumption.
    + inversion H; subst. all: apply IHC in VALA. all: econstructor. all: eassumption.
    + inversion H; subst. all: apply IHC in VALB. all: econstructor. all: eassumption.
    + apply H_equiv in H. assumption.
    + inversion H; subst. all: apply IHC in VALA. all: econstructor. all: eassumption.
    + inversion H; subst. all: apply IHC in VALB. all: econstructor. all: eassumption.
  - intros H_ctx. split. all: (intros; apply (H_ctx Hole); assumption).
Qed.

Module SmallStep.

  Inductive is_value : expr -> Prop :=
    isv_Intro : forall n, is_value (Nat n).
               
  Reserved Notation "st |- e --> e'" (at level 0).

  Inductive ss_step : state Z -> expr -> expr -> Prop :=
    ss_Var   : forall (s   : state Z)
                      (i   : id)
                      (z   : Z)
                      (VAL : s / i => z), (s |- (Var i) --> (Nat z))
  | ss_Left  : forall (s      : state Z)
                      (l r l' : expr)
                      (op     : bop)
                      (LEFT   : s |- l --> l'), (s |- (Bop op l r) --> (Bop op l' r))
  | ss_Right : forall (s      : state Z)
                      (l r r' : expr)
                      (op     : bop)
                      (RIGHT  : s |- r --> r'), (s |- (Bop op l r) --> (Bop op l r'))
  | ss_Bop   : forall (s       : state Z)
                      (zl zr z : Z)
                      (op      : bop)
                      (EVAL    : [| Bop op (Nat zl) (Nat zr) |] s => z), (s |- (Bop op (Nat zl) (Nat zr)) --> (Nat z))      
  where "st |- e --> e'" := (ss_step st e e').

  #[export] Hint Constructors ss_step : core.

  Reserved Notation "st |- e ~~> e'" (at level 0).
  
  Inductive ss_reachable st e : expr -> Prop :=
    reach_base : st |- e ~~> e
  | reach_step : forall e' e'' (HStep : SmallStep.ss_step st e e') (HReach : st |- e' ~~> e''), st |- e ~~> e''
  where "st |- e ~~> e'" := (ss_reachable st e e').
  
  #[export] Hint Constructors ss_reachable : core.

  Reserved Notation "st |- e -->> e'" (at level 0).

  Inductive ss_eval : state Z -> expr -> expr -> Prop :=
    se_Stop : forall (s : state Z)
                     (z : Z),  s |- (Nat z) -->> (Nat z)
  | se_Step : forall (s : state Z)
                     (e e' e'' : expr)
                     (HStep    : s |- e --> e')
                     (Heval    : s |- e' -->> e''), s |- e -->> e''
  where "st |- e -->> e'"  := (ss_eval st e e').
  
  #[export] Hint Constructors ss_eval : core.

  Lemma ss_eval_reachable s e e' (HE: s |- e -->> e') : s |- e ~~> e'.
  Proof. 
    induction HE.
    - constructor.
    - apply reach_step with e'; assumption.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z).
    induction HR; subst.
    - constructor.
    - econstructor; eauto.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.
  
  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof.
    revert e'' H2; induction H1; intros.
    - apply se_Step with e''; auto.
      inversion H2; auto.
    - apply se_Step with e'; auto.
  Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1.
    - assumption.
    - apply reach_step with e'; auto.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof. 
    intros s [e' H_step].
    inversion HV; subst.
    inversion H_step.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. 
    intros H.
    pose (counter_example := Bop And (Nat 2) (Nat 2)).
    assert (Hnot_value: ~ is_value counter_example).
    { intros Hvalue. inversion Hvalue. }
    assert (Hnormal: normal_form counter_example).
    { unfold normal_form, counter_example. intros s [e' Hstep].
      inversion Hstep; subst.
      - inversion LEFT.
      - inversion RIGHT.  
      - inversion EVAL; subst.
        inversion VALA; subst.
        unfold zbool in BOOLA.
        destruct BOOLA as [H2eq | H2eq]; discriminate H2eq. }
    specialize (H counter_example Hnormal).
    contradiction.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    intros H.
    pose (subexpr := Nat 1 [+] Nat 1).
    pose (example := subexpr [+] subexpr).
    assert (Hstep_left: [] |- example --> (Nat 2 [+] subexpr)).
    { unfold example, subexpr.
      apply ss_Left.
      apply ss_Bop.
      replace 2%Z with (1 + 1)%Z by reflexivity.
      apply bs_Add; apply bs_Nat. }
    assert (Hstep_right: [] |- example --> (subexpr [+] Nat 2)).
    { unfold example, subexpr.
      apply ss_Right.
      apply ss_Bop.
      replace 2%Z with (1 + 1)%Z by reflexivity.
      apply bs_Add; apply bs_Nat. }
    specialize (H example (Nat 2 [+] subexpr) (subexpr [+] Nat 2) []).
    specialize (H Hstep_left Hstep_right).
    unfold subexpr in H.
    injection H as Heq.
    inversion Heq.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. dependent destruction H1; dependent destruction H2.
  { specialize (state_deterministic _ _ _  _ _ VAL VAL0) as Heq. rewrite Heq. reflexivity. }
  { inversion H2. }
  { inversion H2. }
  { specialize (eval_deterministic _ _ _ _ EVAL EVAL0) as Heq. rewrite Heq. reflexivity. }
Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. 
    induction Heval.
    - constructor.
    - assumption.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction C.
    - simpl. exact HR.
    - simpl. induction IHC.
      + apply reach_base.
      + subst. eauto.
    - simpl. induction IHC.
      + apply reach_base.
      + subst. eauto.
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof. 
    apply (ss_subst s (BopL op Hole e2)) in HR1.
    apply (ss_subst s (BopR op e1' Hole)) in HR2.
    eapply ss_reachable_trans.
      - apply HR1.
      - apply HR2. 
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H    : [|Bop op e1 e2|] s => z)
    (VALA : [|e1|] s => za)
    (VALB : [|e2|] s => zb) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    inversion H; subst;
      specialize (eval_deterministic e1 s za za0 VALA VALA0) as ->;
      specialize (eval_deterministic e2 s zb zb0 VALB VALB0) as ->;
      eauto.
  Qed.

  #[export] Hint Resolve ss_bop_reachable : core.

  Lemma ss_eval_binop s e1 e2 za zb z op
    (IHe1 : s |- e1 -->> (Nat za))
    (IHe2 : s |- e2 -->> (Nat zb))
    (H    : [|Bop op e1 e2|] s => z)
    (VALA : [|e1|] s => za)
    (VALB : [|e2|] s => zb) :
    s |- Bop op e1 e2 -->> (Nat z).
  Proof.
    apply ss_eval_reachable in IHe1.
    apply ss_eval_reachable in IHe2.
    apply ss_reachable_eval.
    eapply ss_reachable_trans;
      [eapply ss_subst_binop; eassumption | eapply ss_bop_reachable; eassumption].
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

  Lemma ss_eval_equiv (e : expr) (s : state Z) (z : Z) :
    [| e |] s => z <-> s |- e -->> (Nat z).
   Proof.
    split; intros H.
    - dependent destruction H.
      + constructor.
      + apply se_Step with (e':= Nat z).
        * constructor. assumption.
        * constructor.
      + apply se_Step with (e':=Nat(za+zb)).
        * 
  Admitted.

End SmallStep.

Module StaticSemantics.

  Import SmallStep.
  
  Inductive Typ : Set := Int | Bool.

  Reserved Notation "t1 << t2" (at level 0).
  
  Inductive subtype : Typ -> Typ -> Prop :=
  | subt_refl : forall t,  t << t
  | subt_base : Bool << Int
  where "t1 << t2" := (subtype t1 t2).

  Lemma subtype_trans t1 t2 t3 (H1: t1 << t2) (H2: t2 << t3) : t1 << t3.
  Proof. 
    inversion H1; subst.
    - assumption.
    - (* t1 = Bool, t2 = Int *)
      inversion H2; subst.
      (* t2 = t3 = Int, so we need Bool << Int *)
      apply subt_base.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof. 
    inversion H1; subst; inversion H2; subst; reflexivity.
  Qed.
  
  Reserved Notation "e :-: t" (at level 0).
  
  Inductive typeOf : expr -> Typ -> Prop :=
  | type_X   : forall x, (Var x) :-: Int
  | type_0   : (Nat 0) :-: Bool
  | type_1   : (Nat 1) :-: Bool
  | type_N   : forall z (HNbool : ~zbool z), (Nat z) :-: Int
  | type_Add : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [+]  e2) :-: Int
  | type_Sub : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [-]  e2) :-: Int
  | type_Mul : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [*]  e2) :-: Int
  | type_Div : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [/]  e2) :-: Int
  | type_Mod : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [%]  e2) :-: Int
  | type_Lt  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [<]  e2) :-: Bool
  | type_Le  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [<=] e2) :-: Bool
  | type_Gt  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [>]  e2) :-: Bool
  | type_Ge  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [>=] e2) :-: Bool
  | type_Eq  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [==] e2) :-: Bool
  | type_Ne  : forall e1 e2 (H1 : e1 :-: Int ) (H2 : e2 :-: Int ), (e1 [/=] e2) :-: Bool
  | type_And : forall e1 e2 (H1 : e1 :-: Bool) (H2 : e2 :-: Bool), (e1 [&]  e2) :-: Bool
  | type_Or  : forall e1 e2 (H1 : e1 :-: Bool) (H2 : e2 :-: Bool), (e1 [\/] e2) :-: Bool
  where "e :-: t" := (typeOf e t).

  Lemma type_preservation e t t' (HS: t' << t) (HT: e :-: t) : forall st e' (HR: st |- e ~~> e'), e' :-: t'.
  Proof. Abort.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof. 
    remember Bool as zb.
    induction HT; intros; try discriminate; inversion HVal; unfold zbool;
    try solve [right; reflexivity | left; reflexivity].
    - inversion BOOLA; inversion BOOLB.
      { left. rewrite H, H4. reflexivity. }
      all: right; rewrite H, H4; reflexivity.
    - inversion BOOLA; inversion BOOLB; try solve [left; rewrite H, H4; reflexivity].
      * right. rewrite H, H4. reflexivity. 
  Qed.

End StaticSemantics.

Module Renaming.
  
  Definition renaming := { f : id -> id | Bijective f }.
  
  Fixpoint rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.
  
  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
   Proof. destruct r as [f Hbij]. inversion Hbij.
    assert (Bijective x).
    * unfold Bijective. exists f. apply and_comm. assumption.
    * exists (exist Bijective x H0). destruct H. auto.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. destruct r as [f Hbij]. inversion Hbij.
    assert (Bijective x).
    * unfold Bijective. exists f. apply and_comm. assumption.
    * exists (exist Bijective x H0). destruct H. auto.
  Qed.

  Fixpoint rename_expr (r : renaming) (e : expr) : expr :=
    match e with
    | Var x => Var (rename_id r x) 
    | Nat n => Nat n
    | Bop op e1 e2 => Bop op (rename_expr r e1) (rename_expr r e2) 
    end.

  Lemma re_rename_expr
    (r r' : renaming)
    (Hinv : renamings_inv r r')
    (e    : expr) : rename_expr r (rename_expr r' e) = e.
  Proof. 
    induction e.
    - simpl. reflexivity.
    - simpl. rewrite Hinv. reflexivity.
    - simpl. rewrite IHe1, IHe2. reflexivity.
  Qed.
  
  Fixpoint rename_state (r : renaming) (st : state Z) : state Z :=
    match st with
    | [] => []
    | (id, x) :: tl =>
        match r with exist _ f _ => (f id, x) :: rename_state r tl end
    end.

  Lemma re_rename_state
    (r r' : renaming)
    (Hinv : renamings_inv r r')
    (st   : state Z) : rename_state r (rename_state r' st) = st.
  Proof. admit. Admitted.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. 
    inversion BH. inversion H. subst. unfold Injective. intros. congruence.
  Qed.

  Lemma state_renaming_binds_invariance (x : id) (st : state Z) (z : Z) (r : renaming)
    : st / x => z <-> (rename_state r st) / rename_id r x => z.
  Proof.
    split; intros.
    - dependent induction H.
      + dependent destruction r.
        constructor.
      + dependent destruction r.
        constructor.
        * intro. apply H. eapply bijective_injective; eauto.
        * eauto.
    - dependent induction H.
      + dependent destruction r.
        dependent destruction st.
        * inversion x0.
        * dependent destruction p.
          dependent destruction x0.
          apply bijective_injective in b.
          apply b in x.
          subst.
          constructor.
      + dependent destruction r.
        simpl in x0, IHst_binds, H0, H.
        dependent destruction st; inversion x0.
        dependent destruction p.
        dependent destruction H2.
        constructor.
        * unfold "<>". intro.
          assert (x x1 = x i).
          -- rewrite H1. eauto.
          -- contradiction.
        * eapply IHst_binds; eauto.
  Qed.
  
  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    split; intros.
    - dependent induction H; econstructor; eauto.
      + apply state_renaming_binds_invariance. eauto.
    - dependent induction H; dependent destruction e; dependent destruction x; try econstructor; eauto.
      + eapply state_renaming_binds_invariance; eauto.
  Qed.
    
End Renaming.
