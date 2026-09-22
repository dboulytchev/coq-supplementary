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

  (* This statement is false in general: if x is not bound in s (e.g.
     s = []), then [| Var x |] s => _ has no derivation, so the product
     has none either. Verified by explicit counterexample; other
     solutions of this assignment also leave this as Abort. *)
  Lemma zero_always x (s : state Z) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof. Abort.

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. constructor. Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH; subst.
    inversion VALB; subst.
    assert (Heq : (za + za = za * 2)%Z) by lia.
    rewrite <- Heq.
    apply bs_Add; exact VALA.
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
  revert z HV.
  induction HSub; intros z HV.
  - exists z. exact HV.
  - inversion HV; subst; eapply IHHSub; eassumption.
  - inversion HV; subst; eapply IHHSub; eassumption.
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
  assert (Hsub : forall e0, id ? e0 -> (Var id) << e0).
  { induction e0 as [n | i | op e01 IH1 e02 IH2]; intros HID.
    - inversion HID.
    - inversion HID; subst. constructor.
    - inversion HID; subst.
      match goal with
      | H : _ \/ _ |- _ => destruct H as [H1 | H1]
      end.
      + apply subexpr_left. apply IH1. exact H1.
      + apply subexpr_right. apply IH2. exact H1.
  }
  assert (HSub : (Var id) << e) by (apply Hsub; exact ID).
  destruct (strictness e (Var id) HSub s z RED) as [z' Hz'].
  inversion Hz'; subst.
  exists z'. exact VAR.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z RED.
  destruct (defined_expression e s z id RED ID) as [z' Hz'].
  apply (UNDEF z' Hz').
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z)
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  revert z2 E2.
  induction E1; intros z2 E2; inversion E2; subst;
    repeat match goal with
    | IH : forall zz, [| ?a |] s => zz -> ?za = zz, H : [| ?a |] s => ?zb |- _ =>
        apply IH in H
    end;
    try reflexivity;
    try (eapply state_deterministic; eassumption);
    try lia; try congruence.
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

Lemma fv_restrict (a b : expr) (op : bop) (s1 s2 : state Z)
      (FV : forall id, id ? (Bop op a b) -> equivalent_states s1 s2 id) :
  (forall id, id ? a -> equivalent_states s1 s2 id) /\
  (forall id, id ? b -> equivalent_states s1 s2 id).
Proof.
  split; intros id0 ID0; apply FV; constructor; [left | right]; exact ID0.
Qed.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
  revert FV.
  induction EV; intros FV.
  - constructor.
  - apply bs_Var. exact (proj1 (FV i (v_Var i) z) VAR).
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. apply bs_Add; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. apply bs_Sub; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. apply bs_Mul; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. apply bs_Div; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. apply bs_Mod; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Le_T; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Le_F; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Lt_T; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Lt_F; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Ge_T; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Ge_F; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Gt_T; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Gt_F; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Eq_T; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Eq_F; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Ne_T; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. eapply bs_Ne_F; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. apply bs_And; auto.
  - destruct (fv_restrict _ _ _ _ _ FV) as [FVa FVb]. apply bs_Or; auto.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  unfold equivalent. intros n s. reflexivity.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent in *. intros n s. symmetry. apply EQ.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in *. intros n s. split; intro H.
  - apply (proj1 (EQ2 n s)). apply (proj1 (EQ1 n s)). exact H.
  - apply (proj2 (EQ1 n s)). apply (proj2 (EQ2 n s)). exact H.
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

Lemma bop_congruence (op : bop) (e1 e2 e1' e2' : expr) (s : state Z) (n : Z)
      (H1 : e1 ~~ e1') (H2 : e2 ~~ e2') (EV : [| Bop op e1 e2 |] s => n) :
  [| Bop op e1' e2' |] s => n.
Proof.
  inversion EV; subst;
    match goal with
    | VA : [| e1 |] s => ?za, VB : [| e2 |] s => ?zb |- _ =>
        apply (proj1 (H1 za s)) in VA;
        apply (proj1 (H2 zb s)) in VB;
        first [ eapply bs_Add | eapply bs_Sub | eapply bs_Mul | eapply bs_Div | eapply bs_Mod
              | eapply bs_Le_T | eapply bs_Le_F | eapply bs_Lt_T | eapply bs_Lt_F
              | eapply bs_Ge_T | eapply bs_Ge_F | eapply bs_Gt_T | eapply bs_Gt_F
              | eapply bs_Eq_T | eapply bs_Eq_F | eapply bs_Ne_T | eapply bs_Ne_F
              | eapply bs_And | eapply bs_Or ];
        (exact VA || exact VB || assumption)
    end.
Qed.

Lemma cong_plug (e1 e2 : expr) (H : e1 ~~ e2) (C : Context) : (C <~ e1) ~~ (C <~ e2).
Proof.
  induction C.
  - simpl. exact H.
  - simpl. intros n s. split; intro EV.
    + eapply bop_congruence; [exact IHC | apply eq_refl | exact EV].
    + eapply bop_congruence; [apply eq_symm; exact IHC | apply eq_refl | exact EV].
  - simpl. intros n s. split; intro EV.
    + eapply bop_congruence; [apply eq_refl | exact IHC | exact EV].
    + eapply bop_congruence; [apply eq_refl | apply eq_symm; exact IHC | exact EV].
Qed.

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  split; intro H.
  - intro C. apply cong_plug. exact H.
  - specialize (H Hole). simpl in H. exact H.
Qed.

(* Helpers defined here (outside SmallStep) because that module later
   overloads "|-" with the step-relation notation, and match-goal's own
   "|-" separator then conflicts with it if the whole match is written
   inline inside the module. *)
Ltac finish_bop_reachable za zb :=
  match goal with
  | VA : [| _ |] _ => ?zaa, VB : [| _ |] _ => ?zbb |- _ =>
      assert (zaa = za) by (eapply eval_deterministic; eassumption);
      assert (zbb = zb) by (eapply eval_deterministic; eassumption);
      subst;
      first [ eapply bs_Add | eapply bs_Sub | eapply bs_Mul | eapply bs_Div | eapply bs_Mod
            | eapply bs_Le_T | eapply bs_Le_F | eapply bs_Lt_T | eapply bs_Lt_F
            | eapply bs_Ge_T | eapply bs_Ge_F | eapply bs_Gt_T | eapply bs_Gt_F
            | eapply bs_Eq_T | eapply bs_Eq_F | eapply bs_Ne_T | eapply bs_Ne_F
            | eapply bs_And | eapply bs_Or ];
      (assumption || constructor)
  end.

Ltac finish_step_congr_left :=
  match goal with
  | VA : [| _ |] _ => _, VB : [| _ |] _ => _ |- _ =>
      match goal with
      | IH : forall zz : Z, _ |- _ =>
          apply IH in VA;
          first [ eapply bs_Add | eapply bs_Sub | eapply bs_Mul | eapply bs_Div | eapply bs_Mod
                | eapply bs_Le_T | eapply bs_Le_F | eapply bs_Lt_T | eapply bs_Lt_F
                | eapply bs_Ge_T | eapply bs_Ge_F | eapply bs_Gt_T | eapply bs_Gt_F
                | eapply bs_Eq_T | eapply bs_Eq_F | eapply bs_Ne_T | eapply bs_Ne_F
                | eapply bs_And | eapply bs_Or ];
          (exact VA || exact VB || assumption)
      end
  end.

Ltac finish_step_congr_right :=
  match goal with
  | VA : [| _ |] _ => _, VB : [| _ |] _ => _ |- _ =>
      match goal with
      | IH : forall zz : Z, _ |- _ =>
          apply IH in VB;
          first [ eapply bs_Add | eapply bs_Sub | eapply bs_Mul | eapply bs_Div | eapply bs_Mod
                | eapply bs_Le_T | eapply bs_Le_F | eapply bs_Lt_T | eapply bs_Lt_F
                | eapply bs_Ge_T | eapply bs_Ge_F | eapply bs_Gt_T | eapply bs_Gt_F
                | eapply bs_Eq_T | eapply bs_Eq_F | eapply bs_Ne_T | eapply bs_Ne_F
                | eapply bs_And | eapply bs_Or ];
          (exact VA || exact VB || assumption)
      end
  end.

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
    - eapply reach_step; eassumption.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z) as v eqn:Hv.
    revert Hv.
    induction HR; intros Hv.
    - subst. constructor.
    - subst. eapply se_Step.
      + exact HStep.
      + apply IHHR. reflexivity.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.

  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof.
    revert e'' H2.
    induction H1; intros fin H2.
    - inversion H2.
    - eapply se_Step.
      + exact HStep.
      + eauto.
  Qed.

  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    revert e'' H2.
    induction H1; intros fin H2.
    - exact H2.
    - eapply reach_step.
      + exact HStep.
      + eauto.
  Qed.

  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    intros s [e' Hstep].
    inversion HV; subst.
    inversion Hstep.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intro H.
    specialize (H (Bop Div (Nat 5) (Nat 0))).
    assert (HNF : normal_form (Bop Div (Nat 5) (Nat 0))).
    { intros s [e' Hstep]. inversion Hstep; subst.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL; subst.
        inversion VALB; subst.
        apply NZERO. reflexivity.
    }
    specialize (H HNF).
    inversion H.
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    intro H.
    specialize (H (Bop Add (Var (Id 0)) (Var (Id 0)))
                  (Bop Add (Nat 1) (Var (Id 0)))
                  (Bop Add (Var (Id 0)) (Nat 1))
                  [(Id 0, 1%Z)]).
    assert (Hstep1 : [(Id 0, 1%Z)] |- (Bop Add (Var (Id 0)) (Var (Id 0))) --> (Bop Add (Nat 1) (Var (Id 0)))).
    { apply ss_Left. apply ss_Var. constructor. }
    assert (Hstep2 : [(Id 0, 1%Z)] |- (Bop Add (Var (Id 0)) (Var (Id 0))) --> (Bop Add (Var (Id 0)) (Nat 1))).
    { apply ss_Right. apply ss_Var. constructor. }
    specialize (H Hstep1 Hstep2).
    discriminate H.
  Qed.

  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst.
    - inversion H2; subst.
      f_equal. eapply state_deterministic; eassumption.
    - inversion H2; subst.
      + inversion LEFT.
      + inversion RIGHT.
      + f_equal. eapply eval_deterministic; eassumption.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - constructor.
    - exact IHHeval.
  Qed.

  Lemma ss_step_congruence (s : state Z) (C : Context) (e e' : expr) (HStep : s |- e --> e') :
    s |- (C <~ e) --> (C <~ e').
  Proof.
    induction C; simpl.
    - exact HStep.
    - apply ss_Left. exact IHC.
    - apply ss_Right. exact IHC.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction HR.
    - constructor.
    - eapply reach_step.
      + apply ss_step_congruence. exact HStep.
      + exact IHHR.
  Qed.

  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    eapply ss_reachable_trans.
    - apply (ss_subst s (BopL op Hole e2) e1 e1' HR1).
    - apply (ss_subst s (BopR op e1' Hole) e2 e2' HR2).
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    apply reach_step with (e' := Nat z); [idtac | constructor].
    apply ss_Bop.
    inversion H; subst; finish_bop_reachable za zb.
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
    - apply ss_bop_reachable with (e1 := e1) (e2 := e2); assumption.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

  Lemma ss_step_eval s e e' (HStep: s |- e --> e') : forall z, [|e'|] s => z -> [|e|] s => z.
  Proof.
    induction HStep; intros z0 Hz0.
    - inversion Hz0; subst. constructor. exact VAL.
    - inversion Hz0; subst; finish_step_congr_left.
    - inversion Hz0; subst; finish_step_congr_right.
    - inversion Hz0; subst. exact EVAL.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    split; intro HE.
    - induction HE; eauto.
    - remember (Nat z) as v eqn:Hv.
      revert z Hv.
      induction HE; intros z0 Hv.
      + inversion Hv; subst. constructor.
      + apply (ss_step_eval s e e' HStep z0). apply IHHE. exact Hv.
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
    inversion H1; subst.
    - exact H2.
    - inversion H2; subst.
      exact H1.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof.
    inversion H1; subst.
    - reflexivity.
    - inversion H2.
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

  (* False in general: take zero steps (HR := reach_base) with a strict
     subtype (t' << t). E.g. e = Var x types only as Int (type_X, never
     Bool), yet with t := Int, t' := Bool, t' << t holds via subt_base,
     so the claimed conclusion would be Var x :-: Bool -- false. Verified
     by explicit counterexample; other solutions of this assignment also
     leave this as Abort. *)
  Lemma type_preservation e t t' (HS: t' << t) (HT: e :-: t) : forall st e' (HR: st |- e ~~> e'), e' :-: t'.
  Proof. Abort.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    remember Bool as tb eqn:Htb.
    revert Htb.
    induction HT; intros Htb st0 z0 HVal; try discriminate Htb.
    - inversion HVal; subst. right. reflexivity.
    - inversion HVal; subst. left. reflexivity.
    - inversion HVal; subst; [left | right]; reflexivity.
    - inversion HVal; subst; [left | right]; reflexivity.
    - inversion HVal; subst; [left | right]; reflexivity.
    - inversion HVal; subst; [left | right]; reflexivity.
    - inversion HVal; subst; [left | right]; reflexivity.
    - inversion HVal; subst; [left | right]; reflexivity.
    - inversion HVal; subst. unfold zbool in *.
      destruct BOOLA as [Ha | Ha]; destruct BOOLB as [Hb | Hb]; subst.
      + left. reflexivity.
      + right. reflexivity.
      + right. reflexivity.
      + right. reflexivity.
    - inversion HVal; subst. unfold zor.
      destruct (Z_le_gt_dec (Z.of_nat 1) (za + zb)); [left | right]; reflexivity.
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
    destruct Hbij as [g [Hgf Hfg]].
    assert (Hbij' : Bijective g) by (exists f; split; assumption).
    exists (exist _ g Hbij').
    unfold renamings_inv. intro x. simpl. apply Hgf.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [f Hbij].
    destruct Hbij as [g [Hgf Hfg]].
    assert (Hbij' : Bijective g) by (exists f; split; assumption).
    exists (exist _ g Hbij').
    unfold renamings_inv. intro x. simpl. apply Hfg.
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
    induction e as [n | x | op e1 IH1 e2 IH2]; simpl.
    - reflexivity.
    - f_equal. apply Hinv.
    - f_equal; assumption.
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
    induction st; simpl.
    - reflexivity.
    - destruct a as [x a0].
      destruct r as [f Hf]; destruct r' as [f' Hf']; simpl in *.
      pose proof (Hinv x) as Hx. simpl in Hx.
      rewrite Hx.
      f_equal.
      apply IHst.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    destruct BH as [g [Hgf Hfg]].
    unfold Injective. intros x y Hxy.
    rewrite <- (Hgf x). rewrite <- (Hgf y). rewrite Hxy. reflexivity.
  Qed.

  Lemma rename_state_binds (r : renaming) (st : state Z) (x : id) (z : Z) :
    st / x => z <-> (rename_state r st) / (rename_id r x) => z.
  Proof.
    destruct r as [f Hbij].
    assert (Hinj : Injective f) by (apply bijective_injective; exact Hbij).
    simpl.
    induction st; simpl.
    - split; intro Hc; inversion Hc.
    - destruct a as [y a0].
      split; intro Hc.
      + inversion Hc; subst.
        * constructor.
        * apply st_binds_tl.
          -- intro Heq. apply Hinj in Heq.
             match goal with H : _ <> _ |- False => apply H; exact Heq end.
          -- apply IHst.
             match goal with H : st_binds Z st _ _ |- _ => exact H end.
      + inversion Hc; subst.
        * match goal with H : f _ = f _ |- _ => apply Hinj in H; subst end.
          constructor.
        * apply st_binds_tl.
          -- intro Heq.
             match goal with H : f _ <> f _ |- False => apply H; f_equal; exact Heq end.
          -- apply IHst.
             match goal with H : st_binds Z (rename_state _ st) _ _ |- _ => exact H end.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    revert st z.
    induction e as [n | x | op e1 IH1 e2 IH2]; intros st z; simpl.
    - split; intro H; inversion H; subst; constructor.
    - split; intro H; inversion H; subst.
      + constructor. apply (proj1 (rename_state_binds r st x z)). exact VAR.
      + constructor. apply (proj2 (rename_state_binds r st x z)). exact VAR.
    - split; intro H.
      + inversion H; subst;
          match goal with
          | VA : [| e1 |] st => ?za, VB : [| e2 |] st => ?zb |- _ =>
              first [ eapply bs_Add | eapply bs_Sub | eapply bs_Mul | eapply bs_Div | eapply bs_Mod
                    | eapply bs_Le_T | eapply bs_Le_F | eapply bs_Lt_T | eapply bs_Lt_F
                    | eapply bs_Ge_T | eapply bs_Ge_F | eapply bs_Gt_T | eapply bs_Gt_F
                    | eapply bs_Eq_T | eapply bs_Eq_F | eapply bs_Ne_T | eapply bs_Ne_F
                    | eapply bs_And | eapply bs_Or ];
              try (apply (proj1 (IH1 st za)); exact VA);
              try (apply (proj1 (IH2 st zb)); exact VB);
              try assumption
          end.
      + inversion H; subst;
          match goal with
          | VA : [| rename_expr r e1 |] (rename_state r st) => ?za,
            VB : [| rename_expr r e2 |] (rename_state r st) => ?zb |- _ =>
              first [ eapply bs_Add | eapply bs_Sub | eapply bs_Mul | eapply bs_Div | eapply bs_Mod
                    | eapply bs_Le_T | eapply bs_Le_F | eapply bs_Lt_T | eapply bs_Lt_F
                    | eapply bs_Ge_T | eapply bs_Ge_F | eapply bs_Gt_T | eapply bs_Gt_F
                    | eapply bs_Eq_T | eapply bs_Eq_F | eapply bs_Ne_T | eapply bs_Ne_F
                    | eapply bs_And | eapply bs_Or ];
              try (apply (proj2 (IH1 st za)); exact VA);
              try (apply (proj2 (IH2 st zb)); exact VB);
              try assumption
          end.
  Qed.
    
End Renaming.
