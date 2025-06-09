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

  Lemma zero_always x (s : state Z) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof. Abort.

  Lemma zero_always_false: exists x (s : state Z), [| Var x [*] Nat 0 |] s => Z.zero -> False.
  Proof.
    exists (Id 0).
    exists [(Id 1, 1 % Z)].
    intros.
    inversion_clear H.
    inversion_clear VALA.
    inversion_clear VAR.
    inversion_clear H0.
  Qed.
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    apply bs_Nat.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH.
    inversion VALB.
    replace (za * 2) % Z with (za + za) % Z.
    - apply bs_Add.
      + assumption.
      + assumption. 
    - lia. 
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
  induction HV; inversion HSub;
  try solve [
    apply IHHV1; assumption |
    apply IHHV2; assumption |
    exists n; apply bs_Nat |
    exists z; apply bs_Var; assumption |
    exists (za + zb) % Z; apply bs_Add; assumption |
    exists (za - zb) % Z; apply bs_Sub; assumption |
    exists (za * zb) % Z; apply bs_Mul; assumption |
    exists (Z.div za zb) % Z; apply bs_Div; assumption |
    exists (Z.modulo za zb) % Z; apply bs_Mod; assumption |
    exists Z.one; apply (bs_Le_T _ _ _ za zb); assumption |
    exists Z.zero; apply (bs_Le_F _ _ _ za zb); assumption |
    exists Z.one; apply (bs_Lt_T _ _ _ za zb); assumption |
    exists Z.zero; apply (bs_Lt_F _ _ _ za zb); assumption |
    exists Z.one; apply (bs_Ge_T _ _ _ za zb); assumption |
    exists Z.zero; apply (bs_Ge_F _ _ _ za zb); assumption |
    exists Z.one; apply (bs_Gt_T _ _ _ za zb); assumption |
    exists Z.zero; apply (bs_Gt_F _ _ _ za zb); assumption |
    exists Z.one; apply (bs_Eq_T _ _ _ za zb); assumption |
    exists Z.zero; apply (bs_Eq_F _ _ _ za zb); assumption |
    exists Z.one; apply (bs_Ne_T _ _ _ za zb); assumption |
    exists Z.zero; apply (bs_Ne_F _ _ _ za zb); assumption |
    exists (za * zb) % Z; apply bs_And; assumption |
    exists (zor za zb); apply bs_Or; assumption
  ].
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
  induction e; intros; inversion RED; inversion ID;
  try solve [
  subst; exists z; assumption |
  destruct H8; 
    try solve [
      apply IHe1 with (z := za); assumption; assumption |
      apply IHe2 with (z := zb); assumption; assumption
    ]
  ].
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. 
  induction e; intros z' HLeft; inversion ID; inversion HLeft.
  - specialize UNDEF with z'. subst. contradiction.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
  - destruct H3. apply IHe1 with (z := za). assumption. assumption. apply IHe2 with (z := zb). assumption. assumption.
Qed.



(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z2.
  induction E1; intros; inversion E2; subst; eauto; try solve [
    apply (state_deterministic Z s i z z2); assumption; assumption |
    specialize IHE1_1 with (z2 := za0);
    specialize IHE1_2 with (z2 := zb0);
    apply IHE1_1 in VALA;
    apply IHE1_2 in VALB;
    subst;
    reflexivity |
    specialize IHE1_1 with (z2 := za0);
    specialize IHE1_2 with (z2 := zb0);
    apply IHE1_1 in VALA;
    apply IHE1_2 in VALB;
    subst;
    contradiction
  ].
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
  induction EV; eauto.
  - econstructor; eapply FV; [constructor | assumption].
  - econstructor; [apply IHEV1 | apply IHEV2]; intros; eapply FV; eauto.
  - econstructor; [apply IHEV1 | apply IHEV2]; intros; eapply FV; eauto.
  - econstructor; [apply IHEV1 | apply IHEV2]; intros; eapply FV; eauto.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
    + assumption. 
  - econstructor.
    + apply IHEV1. intros. eapply FV. eauto.
    + apply IHEV2. intros. eapply FV. eauto.
    + assumption.
    + assumption.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  unfold equivalent.
  reflexivity.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  split; apply EQ.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  split; intros.
  - apply EQ2. apply EQ1. assumption.
  - apply EQ1. apply EQ2. assumption.
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
split; intros; unfold contextual_equivalent, equivalent in *.
- induction C; try assumption.
  + split; intros HLeft;
    inversion HLeft; subst;
    econstructor; apply IHC in VALA; eauto.
  + intros. split; intros HLeft;
    inversion HLeft; subst;
    econstructor; apply IHC in VALB; eauto.
- specialize H with (C := Hole).
  apply H.
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
    - apply reach_base. 
    - apply reach_step with (e' := e') (e'' := e''); assumption.  
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z) as nz.
    induction HR.
    - subst. apply se_Stop.
    - apply se_Step with (e' := e') (e'' := e'').
      + assumption.
      + apply IHHR in Heqnz. assumption.     
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
    - apply IHss_eval in H2. 
      apply se_Step with (e := e) (e' := e') (e'' := e''); assumption.    
  Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1.
    - assumption.
    - apply IHss_reachable in H2.
      apply reach_step with (e := e) (e' := e'); assumption.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    unfold normal_form. intros s [e' HStep].
    inversion HV. subst. inversion HStep.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. 
    unfold normal_form.
    unfold not.
    intros.
    remember ((Nat 1) [\/] (Nat 2)) as not_value.
    specialize H with not_value.
    assert (HNotValue: (~ (is_value not_value))).
    - unfold not. intros. inversion H0. subst. inversion H1.
    - apply HNotValue. apply H. subst. intros. inversion H0. inversion H1.
      + inversion LEFT.
      + inversion RIGHT.
      + inversion_clear H0. inversion EVAL. inversion VALB. subst. inversion BOOLB.
        * discriminate.
        * discriminate.  
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    unfold not.
    remember (Var (Id 0) [+] Var (Id 0)) as e.
    remember (Var (Id 0) [+] Nat (Z.zero)) as e'.
    remember (Nat (Z.zero) [+] Var (Id 0)) as e''.
    remember ([(Id 0, Z.zero)]) as s.
    intros.
    specialize H with 
      (e := e) 
      (e' := e')
      (e'' := e'')
      (s := s).
    assert (HNeq: e' <> e'').
    - subst. intuition. inversion H0.
    - apply HNeq in H; subst.
      + assumption.
      + apply ss_Right. apply ss_Var. apply st_binds_hd.
      + apply ss_Left. apply ss_Var. apply st_binds_hd.     
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; inversion H2; subst.
    - f_equal. inversion H5. subst. apply (state_deterministic Z s i z1 z). assumption. assumption.
    - inversion H2.
    - inversion H2.
    - inversion H5.
    - inversion H5.
    - injection H5 as E1 E2 E3. subst.
      destruct op; subst; inversion LEFT.
    - injection H5 as E1 E2 E3. subst.
      destruct op; subst; inversion RIGHT.
    - f_equal. injection H5 as E1 E2 E3. subst.
      remember (Bop op (Nat zl) (Nat zr)).
      destruct op; apply (eval_deterministic e s); assumption.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - apply isv_Intro.
    - assumption. 
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction C; subst; simpl.
    - assumption.
    - induction IHC; subst; simpl.
      + apply reach_base.
      + assert (Hss: (s) |- (Bop b e1 e0) --> (Bop b e'0 e0)).
        apply ss_Left. assumption.
        apply (reach_step s (Bop b e1 e0) (Bop b e'0 e0) (Bop b e'' e0) Hss IHIHC).
    - induction IHC.
      + apply reach_base.
      + assert (Hss: (s) |- (Bop b e0 e1) --> (Bop b e0 e'0)).
        apply ss_Right. assumption.
        apply (reach_step s (Bop b e0 e1) (Bop b e0 e'0) (Bop b e0 e'') Hss IHIHC).
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    induction HR1; induction HR2.
    - apply reach_base.
    - apply reach_step with (e' := Bop op e e').
      + apply ss_Right. assumption.
      + assumption.
    - apply reach_step with (e' := Bop op e' e0).
      + apply ss_Left. assumption.
      + assumption.
    - apply reach_step with (e' := Bop op e' e0).
      + apply ss_Left. assumption.        
      + assumption. 
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    apply reach_step with (e' := Nat z).
    - inversion H; subst; apply ss_Bop;
      assert (Hzaeq: za = za0); assert (Hzbeq: zb = zb0);
      try solve [
        apply (eval_deterministic e1 s); assumption |
        apply (eval_deterministic e2 s); assumption
      ]; subst.
      + apply bs_Add. apply bs_Nat. apply bs_Nat.
      + apply bs_Sub. apply bs_Nat. apply bs_Nat.
      + apply bs_Mul. apply bs_Nat. apply bs_Nat.
      + apply bs_Div. apply bs_Nat. apply bs_Nat. assumption.
      + apply bs_Mod. apply bs_Nat. apply bs_Nat. assumption.
      + apply (bs_Le_T _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Le_F _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Lt_T _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Lt_F _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Ge_T _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Ge_F _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Gt_T _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Gt_F _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Eq_T _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Eq_F _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Ne_T _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply (bs_Ne_F _ _ _ za0 zb0). apply bs_Nat. apply bs_Nat. assumption. 
      + apply bs_And. apply bs_Nat. apply bs_Nat. assumption. assumption. 
      + apply bs_Or. apply bs_Nat. apply bs_Nat. assumption. assumption.
    - apply reach_base.  
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
    apply ss_eval_reachable in IHe1, IHe2.
    apply ss_reachable_trans with (e' := Bop op e1 (Nat zb)).
    - apply ss_subst_binop.
      + apply reach_base.
      + assumption.
    - apply ss_reachable_trans with (e' := Bop op (Nat za) (Nat zb)).
      + apply ss_subst_binop.
        * assumption.
        * apply reach_base.
      + apply (ss_bop_reachable s e1 e2 op za zb z); assumption.
  Qed.

  

  #[export] Hint Resolve ss_eval_binop : core.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. admit. Admitted.
  
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
    inversion H1; inversion H2; subst; try solve [
      apply subt_refl |
      apply subt_base
    ].
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof.
    inversion H1; inversion H2; subst; eauto.
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

  Lemma type_preservation_false : ~ (forall e e' t t' st (HS: t' << t) (HT: e :-: t) (HR: st |- e ~~> e'), e' :-: t'). 
  Proof.
    unfold not. 
    intros.
    specialize H with (Var (Id 0)) (Var (Id 0)) Int Bool [].
    assert (HSubt: Bool << Int). apply subt_base.
    apply H in HSubt.
    - inversion HSubt.
    - apply type_X.
    - apply reach_base.    
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof. 
    remember Bool as zb.
    induction HT; intros; try discriminate; inversion HVal;
    subst; simpl; unfold zbool; 
    try solve [
      left; auto |
      right; auto
    ].
    - subst; unfold zbool; inversion BOOLA; inversion BOOLB; 
      subst; simpl; try solve [
        left; auto |
        right; auto
      ].
    - subst; unfold zbool; inversion BOOLA; inversion BOOLB; 
      subst; simpl; try solve [
        left; auto |
        right; auto
      ]. 
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
    destruct r as [f Hbij].
    destruct Hbij as [g Hfg].
    assert (Bijective g).
    - exists f. split.
      * intros. apply (proj2 Hfg).
      * intros. apply (proj1 Hfg).
    - exists (exist _ g H).
      unfold renamings_inv, rename_id.
      intros.
      apply Hfg.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [f Hbij].
    destruct Hbij as [g Hfg].
    assert (Bijective g).
    - exists f. split.
      * intros. apply (proj2 Hfg).
      * intros. apply (proj1 Hfg).
    - exists (exist Bijective g H).
      unfold renamings_inv, rename_id.
      intros.
      apply Hfg.
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
    - simpl. 
      f_equal.
      apply Hinv.
    - simpl.
      f_equal.
      + apply IHe1.
      + apply IHe2.
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
    - simpl.
      destruct r as [f Hbf]. 
      destruct r' as [g Hbg].
      destruct a as [id v].
      simpl.
      f_equal.
      + unfold renamings_inv, rename_id in Hinv.
        f_equal.
        apply Hinv.
      + apply IHst.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    unfold Bijective in BH.
    unfold Injective.
    destruct BH as [g [Hfg Hgf]].
    intros x y H.
    apply (f_equal g) in H.
    rewrite Hfg, Hfg in H.
    assumption.
  Qed.
  
  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. admit. Admitted.
    
End Renaming.
