Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

Require Import List.
Import ListNotations.

From hahn Require Import HahnBase.
Require Import Coq.Program.Equality.

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

  Lemma zero_always x (s : state Z) (v : Z) (EVALH: s / x => v) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof.
    remember (bs_Nat s Z.zero).
    remember (bs_Var s x v EVALH).
    remember (bs_Mul s (Var x) (Nat 0) v 0%Z e0 e). (* e1 *)
    clear Heqe1.
    rewrite (Z.mul_0_r v) in e1.
    apply e1.
  Qed.
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    intros.
    apply bs_Nat.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    intros.
    inversion HH. subst.
    inversion VALB. subst.
    assert ((za * 2)%Z = (za + za)%Z). intuition.
    rewrite H.
    apply bs_Add; assumption.
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
  intros.
  generalize dependent z.
  induction HSub; intros.
    - exists z. assumption.
    - inversion HV; subst; apply (IHHSub za); apply VALA.
    - inversion HV; subst; apply (IHHSub zb); apply VALB.
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
  intros.
  generalize dependent z.
  induction e; intros; inversion ID; subst.
    - inversion RED. subst. exists z. assumption.
    - inversion RED; subst; destruct H3; eauto.
Qed.


(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  generalize dependent UNDEF.
  induction e; intros; inversion ID; subst.
  - unfold not. intros. inversion H. subst. specialize (UNDEF z). contradiction.
  - inversion H3; intuition; inversion H0; eauto.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z1.
  generalize dependent z2.
  induction e.
    - intros. inversion E1. inversion E2. subst. reflexivity.
    - intros. inversion E1. inversion E2. subst. remember (state_deterministic Z s i z1 z2). clear Heqe. specialize (e VAR). specialize (e VAR0). assumption.
    - intros. inversion E1; inversion E2; subst; remember (IHe1 za VALA za0 VALA0); remember (IHe2 zb VALB zb0 VALB0); congruence.
Qed.

Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof. 
  intros.
  generalize dependent z.
  induction e.
    - intros. inversion EV. subst. apply bs_Nat.
    - intros. inversion EV. subst. apply FV in VAR.
      + constructor. assumption.
      + apply v_Var.
    - intros. inversion EV; subst; econstructor; eauto.
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
Proof. 
  unfold equivalent in EQ1.
  unfold equivalent in EQ2.
  unfold equivalent.
  intros. split.
    - intros. apply EQ2. apply EQ1. assumption.
    - intros. apply EQ1. apply EQ2. assumption.
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
  - intro. split; intros; generalize dependent n; induction C; intros.
    + apply H in H0. assumption.
    + inversion H0; subst. all: apply IHC in VALA. all: econstructor. all: eassumption.
    + inversion H0; subst. all: apply IHC in VALB. all: econstructor. all: eassumption.
    + apply H in H0. assumption.
    + inversion H0; subst. all: apply IHC in VALA. all: econstructor. all: eassumption.
    + inversion H0; subst. all: apply IHC in VALB. all: econstructor. all: eassumption.
  - intro. split. all: (intros; apply (H Hole); assumption).
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
    induction HE; subst.
      - apply reach_base.
      - apply reach_step with e'; assumption.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof. 
    remember (Nat z) as ze.
    induction HR.
      - rewrite Heqze. apply se_Stop.
      - subst. eauto.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.
  
  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof. 
    induction H1.
      - inversion H2.
      - apply se_Step with e'.
        + assumption.
        + specialize (IHss_eval H2). assumption.
  Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof. 
    induction H1.
      - inversion H2.
        + rewrite H in H2. subst. apply reach_base.
        + apply reach_step with e'; assumption.
      - apply reach_step with e'.
        + assumption.
        + specialize (IHss_reachable H2). assumption.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof. 
    intro. intro. inversion HV. subst. destruct H. inversion H.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. 
    remember ((Nat 1) [/] (Nat 0)) as CE.
    assert (normal_form CE) as NF.
      - intro. intro. inv H. inversion H0.
        + inversion LEFT.
        + inversion RIGHT.
        + inversion EVAL. inversion VALB. subst. contradiction.
      - intro. specialize (H CE). apply H in NF. inversion NF. rewrite HeqCE in H0. inversion H0. 
  Qed.
        
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. 
    intro. 
    (* x + y, x = 0, y = 1 *)
    remember (Var (Id 0)) as l.
    remember (Var (Id 1)) as r.
    remember ([(Id 0, Z.zero) ; (Id 1, Z.one)] : state Z) as state.
    remember (H (l [+] r) ((Nat 0) [+] r) (l [+] (Nat 1)) state).
    assert ((state) |- l [+] r --> ((Nat 0) [+] r)).
      - constructor. rewrite Heql. rewrite Heqstate. constructor. constructor.
      - assert ((state) |- l [+] r --> (l [+] (Nat 1))).
        + constructor. rewrite Heqr. rewrite Heqstate. constructor. constructor. intuition.
          * inversion H1.
          * constructor.
        + remember (e H0 H1). inversion e0. subst. inversion H3.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. 
    inversion H1; subst; inversion H2; subst.
      - remember (state_deterministic Z s i z z0 VAL VAL0). rewrite e. reflexivity.
      - inversion H2. subst.
        + inversion LEFT.
        + inversion RIGHT.
      - inversion H2.
        + inversion LEFT.
        + inversion RIGHT.
      - inversion H2.
        + remember (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z0 z EVAL0 EVAL). rewrite e. reflexivity.
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
      - auto.
      - simpl. induction IHC.
        + auto.
        + simpl. eauto.
      - simpl. induction IHC.
        + auto.
        + simpl. eauto.
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
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    inversion H; subst;
    specialize (eval_deterministic e1 s za za0 VALA VALA0);
    specialize (eval_deterministic e2 s zb zb0 VALB VALB0);
    intros; subst; eauto.
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
    apply ss_eval_reachable in IHe1.
    apply ss_eval_reachable in IHe2.
    apply ss_reachable_eval.
    eapply ss_reachable_trans.
      - eapply ss_subst_binop; eassumption.
      - eapply ss_bop_reachable; eassumption.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

  Lemma apply_step_to_eval s e e' z
    (STEP : (s) |- e --> e')
    (EVAL : [|e'|] s => z) :
    [|e|] s => (z).
  Proof.
    dependent induction e.
    - inversion STEP.
    - inversion STEP. subst. eauto. inversion EVAL. subst. eauto.
    - dependent induction b.
      all: inversion STEP; subst.
      all: inversion EVAL; subst.
      all: eauto.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. 
    split.
    - intro. generalize dependent z. 
      dependent induction e.
      + intros. inversion H. constructor.
      + intros. inversion H. subst. eauto.
      + intros. inversion H; subst; eauto.
    - intro. dependent induction H.
      + constructor.
      + specialize (IHss_eval z).
        assert (Nat z = Nat z) by reflexivity.
        specialize (IHss_eval H0).
        remember (apply_step_to_eval _ _ _ _ HStep IHss_eval).
        assumption.
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
    induction H1. inversion H2. subst.
      - assumption.
      - inversion H2; subst; assumption.
      - destruct t3. inversion H2. subst. 
        + constructor.
        + inversion H2.
  Qed.


  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof. 
    destruct t1. destruct t2.
    - reflexivity.
    - inversion H1.
    - destruct t2.
      + inversion H2.
      + reflexivity.
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
    induction e; intros; inversion HT; subst.
      - inversion HVal. subst. right. reflexivity.
      - inversion HVal. subst. constructor. reflexivity.
      - inversion HVal; subst.
        + constructor. reflexivity.
        + right. reflexivity.
      - inversion HVal; subst.
        + constructor. reflexivity.
        + right. reflexivity.
      - inversion HVal; subst.
        + constructor. reflexivity.
        + right. reflexivity.
      - inversion HVal; subst.
        + constructor. reflexivity.
        + right. reflexivity.
      - inversion HVal; subst.
        + constructor. reflexivity.
        + right. reflexivity.
      - inversion HVal; subst.
        + constructor. reflexivity.
        + right. reflexivity.
      - inversion HVal. subst. inversion BOOLA; inversion BOOLB; subst.
        + constructor. reflexivity.
        + right. reflexivity.
        + right. simpl. reflexivity.
        + right. reflexivity.
      - inversion HVal. subst. inversion BOOLA; inversion BOOLB; subst.
        + constructor. reflexivity.
        + constructor. reflexivity.
        + constructor. reflexivity.
        + right. reflexivity.
  Qed.

End StaticSemantics.

Module Renaming.
  
  Definition renaming := { f : id -> id | Bijective f }.
  
  Fixpoint rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.
  
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. 
    inversion BH. inversion H. subst. unfold Injective. intros. congruence.
  Qed.

  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof. 
    destruct r. destruct b. destruct a. 
    assert (BH: Bijective x0).
    - unfold Bijective. exists x. split; assumption. 
    - exists (exist _ x0 BH).
      unfold renamings_inv. simpl. intro. specialize (e x1). assumption.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. 
    destruct r. destruct b. destruct a. 
    assert (BH: Bijective x0).
    - unfold Bijective. exists x. split; assumption. 
    - exists (exist _ x0 BH).
      unfold renamings_inv. simpl. intro. specialize (e0 x1). assumption.
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
    - rewrite IHe1. rewrite IHe2. reflexivity.
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
    - simpl. reflexivity.
    - simpl. destruct a. destruct r. destruct r'. simpl. rewrite Hinv. rewrite IHst. reflexivity.
  Qed.

  Lemma state_renameing_invariance (st : state Z) (r : renaming) :
    forall (x : id) (z : Z), st / x => z <-> (rename_state r st) / (rename_id r x) => z.
  Proof.
    split.
    - intros. induction H.
      + simpl. destruct r. constructor.
      + simpl. destruct r. constructor. 
        * intro. unfold "<>" in *. apply H. eapply bijective_injective.
          -- exact b.
          -- eassumption.
        * apply IHst_binds.
    - intros. dependent induction H.
      + dependent destruction r. dependent destruction st.
        * inversion x0.
        * dependent destruction p. dependent destruction x0. apply bijective_injective in b. apply b in x.
         subst. constructor.
      + dependent destruction r. simpl in H, H0, IHst_binds. dependent destruction st. 
        * inversion x0.
        * dependent destruction p. inversion x0. dependent destruction H2. constructor.
          -- intro. apply H. rewrite H1. reflexivity.
          -- eapply IHst_binds. all: reflexivity.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. 
    split.
    - intros. induction H. all: econstructor. all: eauto.
      + apply state_renameing_invariance. assumption.
    - intros. dependent induction H. all: dependent destruction e. all: dependent destruction x. all: eauto.
      + constructor. eapply state_renameing_invariance. eassumption.
  Qed.
    
End Renaming.
