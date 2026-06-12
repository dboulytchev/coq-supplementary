Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

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

(* Big-step evaluation relation *)
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

  Lemma zero_always x (s : state Z) n
        (VAR : s / x => n) :
    [| Var x [*] Nat 0 |] s => Z.zero.
  Proof.
    assert (HZ : (n * 0)%Z = Z.zero) by apply Z.mul_0_r.
    rewrite <- HZ.
    eapply bs_Mul.
    - constructor. exact VAR.
    - constructor.
  Qed.

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    constructor.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH; subst.
    inversion VALB; subst.
    replace (za * 2)%Z with (za + za)%Z by lia.
    eapply bs_Add; eauto.
  Qed.
  
End SmokeTest.

(* A relation of one expression being of a subexpression of another *)
Reserved Notation "e1 << e2" (at level 0).

Inductive subexpr : expr -> expr -> Prop :=
  subexpr_refl : forall e : expr, e << e
| subexpr_left : forall e e' e'' : expr, forall op : bop, e << e' -> e << (Bop op e' e'')
| subexpr_right : forall e e' e'' : expr, forall op : bop, e << e'' -> e << (Bop op e' e'')
where "e1 << e2" := (subexpr e1 e2).

Lemma strictness (e e' : expr) (HSub : e' << e) (st : state Z) (z : Z) (HV : [| e |] st => z) :
  exists z' : Z, [| e' |] st => z'.
Proof.
  revert e' HSub.
  induction HV; intros e' HSub; inversion HSub; subst; eauto.
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
  induction RED; inversion ID; subst; eauto;
    match goal with
    | H : _ \/ _ |- _ => destruct H; eauto
    end.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z EV.
  destruct (defined_expression e s z id EV ID) as [z' BIND].
  exact (UNDEF z' BIND).
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  revert z2 E2.
  induction E1; intros z2 E2; inversion E2; subst; try reflexivity;
    try (assert (za = za0) by eauto;
         assert (zb = zb0) by eauto;
         subst; try reflexivity; try lia; try congruence).
  - eapply state_deterministic; eauto.
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
  revert s2 FV.
  induction EV; intros s2 FV.
  - constructor.
  - constructor.
    destruct (FV i (v_Var i) z) as [H _].
    exact (H VAR).
  - eapply bs_Add.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
  - eapply bs_Sub.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
  - eapply bs_Mul.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
  - eapply bs_Div.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact NZERO.
  - eapply bs_Mod.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact NZERO.
  - eapply bs_Le_T.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Le_F.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Lt_T.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Lt_F.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Ge_T.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Ge_F.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Gt_T.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Gt_F.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Eq_T.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Eq_F.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Ne_T.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_Ne_F.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact OP.
  - eapply bs_And.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact BOOLA.
    + exact BOOLB.
  - eapply bs_Or.
    + eapply IHEV1. intros id ID. apply FV. constructor. left. exact ID.
    + eapply IHEV2. intros id ID. apply FV. constructor. right. exact ID.
    + exact BOOLA.
    + exact BOOLB.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  unfold equivalent.
  tauto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent in *.
  intros n s.
  specialize (EQ n s).
  tauto.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in *.
  intros n s.
  specialize (EQ1 n s).
  specialize (EQ2 n s).
  tauto.
Qed.

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
  - intros EQ C.
    induction C; simpl; auto.
    + unfold equivalent in *.
      intros n s; split; intro EV; inversion EV; subst; eauto.
      all: apply IHC in VALA; eauto.
    + unfold equivalent in *.
      intros n s; split; intro EV; inversion EV; subst; eauto.
      all: apply IHC in VALB; eauto.
  - intros CEQ.
    specialize (CEQ Hole).
    simpl in CEQ.
    exact CEQ.
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
    induction HE; eauto.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z) as v.
    induction HR; subst; eauto.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.
  
  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof.
    induction H1; eauto.
    inversion H2.
  Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1; eauto.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    inversion HV; subst.
    intros s [e' STEP].
    inversion STEP.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intro H.
    specialize (H (Nat 1 [/] Nat 0)).
    assert (NF : normal_form (Nat 1 [/] Nat 0)).
    { intros s [e' STEP].
      inversion STEP; subst; try inversion LEFT; try inversion RIGHT.
      inversion EVAL; subst.
      inversion VALB; subst.
      apply NZERO.
      reflexivity. }
    pose proof (H NF) as HV.
    inversion HV.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    intro DET.
    set (x := Id 0).
    set (y := Id 1).
    set (s := [(x, 1%Z); (y, 2%Z)]).
    set (e := Var x [+] Var y).
    assert (X : s / x => 1%Z) by constructor.
    assert (Y : s / y => 2%Z).
    { apply st_binds_tl.
      - unfold x, y. congruence.
      - constructor. }
    assert (L : s |- e --> (Nat 1 [+] Var y)) by (apply ss_Left; constructor; exact X).
    assert (R : s |- e --> (Var x [+] Nat 2)) by (apply ss_Right; constructor; exact Y).
    specialize (DET e (Nat 1 [+] Var y) (Var x [+] Nat 2) s L R).
    inversion DET.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst; inversion H2; subst; try inversion LEFT; try inversion RIGHT.
    - f_equal. eapply state_deterministic; eauto.
    - f_equal. eapply eval_deterministic; eauto.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - constructor.
    - exact IHHeval.
  Qed.

  Lemma ss_reachable_left s e e' r op
        (HR : s |- e ~~> e') :
    s |- (Bop op e r) ~~> (Bop op e' r).
  Proof.
    induction HR; eauto.
  Qed.

  Lemma ss_reachable_right s l e e' op
        (HR : s |- e ~~> e') :
    s |- (Bop op l e) ~~> (Bop op l e').
  Proof.
    induction HR; eauto.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction C; simpl; auto.
    - apply ss_reachable_left. auto.
    - apply ss_reachable_right. auto.
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    eapply ss_reachable_trans.
    - apply ss_reachable_left. exact HR1.
    - apply ss_reachable_right. exact HR2.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    apply reach_step with (e' := Nat z).
    - apply ss_Bop.
      inversion H; subst;
        assert (za0 = za) by eauto using eval_deterministic;
        assert (zb0 = zb) by eauto using eval_deterministic;
        subst; eauto.
    - constructor.
  Qed.

  #[export] Hint Resolve ss_bop_reachable : core.
   
  Lemma ss_eval_binop s e1 e2 za zb z op
        (IHe1 : (s) |- e1 -->> (Nat za))
        (IHe2 : (s) |- e2 -->> (Nat zb))
        (H    : [|Bop op e1 e2|] s => z)
        (VALA : [|e1|] s => (za))
        (VALB : [|e2|] s => (zb)) :
        s |- Bop op e1 e2 -->> (Nat z).
  Proof.
    apply ss_reachable_eval.
    eapply ss_reachable_trans.
    - apply ss_subst_binop.
      + apply ss_eval_reachable. exact IHe1.
      + apply ss_eval_reachable. exact IHe2.
    - eapply ss_bop_reachable; eauto.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    assert (STEP_EVAL : forall e e' z,
               s |- e --> e' -> [| e' |] s => z -> [| e |] s => z).
    { intros e0 e'0 res STEP.
      revert res.
      induction STEP; intros res EV; inversion EV; subst; eauto. }
    split.
    - intro EV.
      induction EV; eauto;
        eapply ss_eval_binop; eauto.
    - intro EV.
      remember (Nat z) as v.
      induction EV.
      + inversion Heqv; subst. constructor.
      + eapply STEP_EVAL; eauto.
  Qed.
  
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
    inversion H1; subst; auto.
    inversion H2; subst; auto.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof.
    inversion H1; inversion H2; subst; auto.
  Qed.
  
  Reserved Notation "e :-: t" (at level 0).
  
  Inductive typeOf : expr -> Typ -> Prop :=
  | type_X   : forall x, (Var x) :-: Int
  | type_0   : (Nat 0) :-: Bool
  | type_1   : (Nat 1) :-: Bool
  | type_N   : forall z, (Nat z) :-: Int
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

  Lemma zbool_dec z : {zbool z} + {~ zbool z}.
  Proof.
    unfold zbool.
    destruct (Z.eq_dec z Z.one) as [HONE | HNONE].
    - left; auto.
    - destruct (Z.eq_dec z Z.zero) as [HZERO | HNZERO].
      + left; auto.
      + right. tauto.
  Qed.

  Lemma nat_bool_type z (HB : zbool z) : (Nat z) :-: Bool.
  Proof.
    unfold zbool in HB.
    destruct HB; subst; constructor.
  Qed.

  Lemma nat_int_type z : (Nat z) :-: Int.
  Proof.
    apply type_N.
  Qed.

  Lemma bool_result_type z (EV : [| Nat z |] [] => z) (HB : zbool z) : (Nat z) :-: Bool.
  Proof.
    apply nat_bool_type. exact HB.
  Qed.

  Lemma zbool_mul x y (HX : zbool x) (HY : zbool y) : zbool (x * y).
  Proof.
    unfold zbool in *.
    destruct HX; destruct HY; subst.
    - left. reflexivity.
    - right. reflexivity.
    - right. reflexivity.
    - right. reflexivity.
  Qed.

  Lemma zbool_zor x y : zbool (zor x y).
  Proof.
    unfold zbool, zor.
    destruct (Z_le_gt_dec (Z.of_nat 1) (x + y)); auto.
  Qed.

  Lemma bop_bool_value_type st op zl zr z
        (HT : (Bop op (Nat zl) (Nat zr)) :-: Bool)
        (EV : [| Bop op (Nat zl) (Nat zr) |] st => z) :
    (Nat z) :-: Bool.
  Proof.
    inversion HT; subst; inversion EV; subst; try constructor;
      eauto using nat_bool_type, zbool_mul, zbool_zor.
  Qed.

  Lemma type_step e t st e' (HT : e :-: t) (HS : st |- e --> e') : e' :-: t.
  Proof.
    revert e' HS.
    induction HT; intros e' HS; inversion HS; subst; eauto using nat_int_type.
    all: try solve [constructor; eauto].
    all: try solve [apply nat_int_type].
    all: try solve [eapply bop_bool_value_type; [constructor; eauto | eauto]].
    all: try solve [inversion EVAL; subst; try constructor;
                    eauto using nat_bool_type, zbool_mul, zbool_zor].
  Qed.

  Lemma type_preservation e t (HT: e :-: t) : forall st e' (HR: st |- e ~~> e'), e' :-: t.
  Proof.
    intros st e' HR.
    induction HR.
    - exact HT.
    - apply IHHR.
      eapply type_step; eauto.
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    remember Bool as t.
    induction HT; intros st res HVal; inversion Heqt; subst; inversion HVal; subst;
      eauto using zbool_mul, zbool_zor.
    all: try solve [unfold zbool; auto].
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
  Proof.
    destruct r as [f [g [Hgf Hfg]]].
    exists (exist _ g (ex_intro _ f (conj Hfg Hgf))).
    unfold renamings_inv, rename_id.
    simpl.
    exact Hgf.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [f [g [Hgf Hfg]]].
    exists (exist _ g (ex_intro _ f (conj Hfg Hgf))).
    unfold renamings_inv, rename_id.
    simpl.
    exact Hfg.
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
    induction e; simpl; auto.
    - rewrite Hinv. reflexivity.
    - rewrite IHe1, IHe2. reflexivity.
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
  Proof.
    induction st.
    - reflexivity.
    - destruct a as [x z].
      simpl.
    destruct r as [f Bf].
    destruct r' as [g Bg].
    simpl in *.
    rewrite Hinv, IHst.
    reflexivity.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    destruct BH as [g [Hgf Hfg]].
    unfold Injective.
    intros x y H.
    rewrite <- (Hgf x).
    rewrite <- (Hgf y).
    now rewrite H.
  Qed.

  Lemma renaming_injective (r : renaming) :
    Injective (rename_id r).
  Proof.
    destruct r as [f BH].
    apply bijective_injective.
    exact BH.
  Qed.

  Lemma rename_state_binds_forward (r : renaming) st x z
        (BIND : st / x => z) :
    st_binds Z (rename_state r st) (rename_id r x) z.
  Proof.
    induction BIND; simpl.
    - destruct r as [f BH]. constructor.
    - destruct r as [f BH].
      simpl in *.
      apply st_binds_tl.
      + intro EQ.
        apply H.
        eapply bijective_injective; eauto.
      + exact IHBIND.
  Qed.

  Lemma rename_state_binds (r : renaming) st x z :
    st / x => z <-> st_binds Z (rename_state r st) (rename_id r x) z.
  Proof.
    split.
    - apply rename_state_binds_forward.
    - intro BIND.
      destruct (renaming_inv r) as [r' Hinv].
      pose proof (rename_state_binds_forward r' (rename_state r st) (rename_id r x) z BIND) as BIND'.
      rewrite (re_rename_state r' r Hinv st) in BIND'.
      unfold renamings_inv in Hinv.
      rewrite Hinv in BIND'.
      exact BIND'.
  Qed.

  Lemma eval_renaming_forward (e : expr) (st : state Z) (z : Z) (r: renaming)
        (EV : [| e |] st => z) :
    [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    induction EV; simpl; eauto.
    - constructor.
      apply rename_state_binds.
      exact VAR.
  Qed.
  
  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    split.
    - apply eval_renaming_forward.
    - intro EV.
      destruct (renaming_inv r) as [r' Hinv].
      pose proof (eval_renaming_forward (rename_expr r e) (rename_state r st) z r' EV) as EV'.
      rewrite (re_rename_expr r' r Hinv e) in EV'.
      rewrite (re_rename_state r' r Hinv st) in EV'.
      exact EV'.
  Qed.
    
End Renaming.
