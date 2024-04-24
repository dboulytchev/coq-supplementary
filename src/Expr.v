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

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. apply bs_Nat. Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. inversion HH. inversion VALB. subst.
    assert ((za * 2)%Z = (za + za)%Z). lia.
    rewrite H. apply bs_Add. exact VALA. exact VALA.
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
Proof. generalize dependent z. induction e; intros; inversion HSub.
  exists z. apply bs_Nat.
  exists z. exact HV.
  exists z. exact HV.
  inversion HV; exact (IHe1 H1 za VALA).
  inversion HV; exact (IHe2 H1 zb VALB).
Qed.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (a b : expr) (op : bop), id ? a \/ id ? b -> id ? (Bop op a b)
where "x ? e" := (V e x).

(* If an expression is defined in some state, then each its' variable is
   defined in that state
 *)      
Lemma defined_expression
      (e : expr) (s : state Z) (z : Z) (id : id)
      (RED : [| e |] s => z)
      (ID  : id ? e) :
  exists z', s / id => z'.
Proof. generalize dependent z. induction e.
  intros. inversion ID.
  intros. inversion ID. inversion RED. subst. exists z. exact VAR.
  intros. inversion ID. inversion H3.
  inversion RED; exact (IHe1 H4 za VALA).
  inversion RED; exact (IHe2 H4 zb VALB).
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. intros. intro. remember (defined_expression e s z id H ID). destruct e0. remember (UNDEF x). contradiction. Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. generalize dependent z1. generalize dependent z2. induction e.
  intros. inversion E1. inversion E2. subst. reflexivity.
  intros. inversion E1. inversion E2. subst. exact (state_deterministic Z s i z1 z2 VAR VAR0).
  intros. inversion E1.
    subst. inversion E2. rewrite (IHe1 za VALA za0 VALA0). rewrite (IHe2 zb VALB zb0 VALB0). reflexivity.
    subst. inversion E2. rewrite (IHe1 za VALA za0 VALA0). rewrite (IHe2 zb VALB zb0 VALB0). reflexivity.
    subst. inversion E2. rewrite (IHe1 za VALA za0 VALA0). rewrite (IHe2 zb VALB zb0 VALB0). reflexivity.
    subst. inversion E2. rewrite (IHe1 za VALA za0 VALA0). rewrite (IHe2 zb VALB zb0 VALB0). reflexivity.
    subst. inversion E2. rewrite (IHe1 za VALA za0 VALA0). rewrite (IHe2 zb VALB zb0 VALB0). reflexivity.
    subst. inversion E2. reflexivity. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction.
    subst. inversion E2. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction. reflexivity.
    subst. inversion E2. reflexivity. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction.
    subst. inversion E2. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction. reflexivity.
    subst. inversion E2. reflexivity. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction.
    subst. inversion E2. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction. reflexivity.
    subst. inversion E2. reflexivity. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction.
    subst. inversion E2. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction. reflexivity.
    subst. inversion E2. reflexivity. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction.
    subst. inversion E2. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction. reflexivity.
    subst. inversion E2. reflexivity. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction.
    subst. inversion E2. remember (IHe1 za VALA za0 VALA0). remember (IHe2 zb VALB zb0 VALB0). subst. contradiction. reflexivity.
    subst. inversion E2. rewrite (IHe1 za VALA za0 VALA0). rewrite (IHe2 zb VALB zb0 VALB0). reflexivity.
    subst. inversion E2. rewrite (IHe1 za VALA za0 VALA0). rewrite (IHe2 zb VALB zb0 VALB0). reflexivity.
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

Lemma equivalent_states_for_left_part_of_bop (b : bop) (e1 e2 : expr) (s1 s2 : state Z)
  (FV : forall (i : id), i ? (Bop b e1 e2) -> equivalent_states s1 s2 i) :
  forall (i : id), i ? e1 -> equivalent_states s1 s2 i.
Proof. intros. apply FV. apply v_Bop. left. exact H. Qed.

Lemma equivalent_states_for_right_part_of_bop (b : bop) (e1 e2 : expr) (s1 s2 : state Z)
  (FV : forall (i : id), i ? (Bop b e1 e2) -> equivalent_states s1 s2 i) :
  forall (i : id), i ? e2 -> equivalent_states s1 s2 i.
Proof. intros. apply FV. apply v_Bop. right. exact H. Qed.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof. generalize dependent z. induction e.
  intros. inversion EV. apply bs_Nat.
  intros. inversion EV. remember (FV i (v_Var i) z). destruct i1. apply bs_Var. exact (s0 VAR).
  intros. inversion EV.
    subst. exact (bs_Add  s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Add e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Add e1 e2 s1 s2 FV) zb VALB)).
    subst. exact (bs_Sub  s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Sub e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Sub e1 e2 s1 s2 FV) zb VALB)).
    subst. exact (bs_Mul  s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Mul e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Mul e1 e2 s1 s2 FV) zb VALB)).
    subst. exact (bs_Div  s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Div e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Div e1 e2 s1 s2 FV) zb VALB) NZERO).
    subst. exact (bs_Mod  s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Mod e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Mod e1 e2 s1 s2 FV) zb VALB) NZERO).
    subst. exact (bs_Le_T s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Le  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Le  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Le_F s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Le  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Le  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Lt_T s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Lt  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Lt  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Lt_F s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Lt  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Lt  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Ge_T s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Ge  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Ge  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Ge_F s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Ge  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Ge  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Gt_T s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Gt  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Gt  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Gt_F s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Gt  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Gt  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Eq_T s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Eq  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Eq  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Eq_F s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Eq  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Eq  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Ne_T s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Ne  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Ne  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_Ne_F s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Ne  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Ne  e1 e2 s1 s2 FV) zb VALB) OP).
    subst. exact (bs_And  s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop And e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop And e1 e2 s1 s2 FV) zb VALB) BOOLA BOOLB).
    subst. exact (bs_Or   s2 e1 e2 za zb (IHe1 (equivalent_states_for_left_part_of_bop Or  e1 e2 s1 s2 FV) za VALA) (IHe2 (equivalent_states_for_right_part_of_bop Or  e1 e2 s1 s2 FV) zb VALB) BOOLA BOOLB).
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. intro. intro. tauto. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. intro. intro. destruct (EQ n s). split. auto. auto. Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. intro. intro. destruct (EQ1 n s). destruct (EQ2 n s). split. auto. auto. Qed.

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

Lemma plug_BopL_equiv' (b : bop) (e e1 e2 : expr) (s : state Z)
  (H : forall n : Z, [|e1|] s => n -> [|e2|] s => n) :
  forall n : Z, [|Bop b e1 e|] s => n -> [|Bop b e2 e|] s => n.
Proof. intros. inversion H0.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact (H za VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
Qed.

Lemma plug_BopL_equiv (b : bop) (e e1 e2 : expr) (s : state Z)
  (H : forall n : Z, [|e1|] s => n <-> [|e2|] s => n) :
  forall n : Z, [|Bop b e1 e|] s => n <-> [|Bop b e2 e|] s => n.
Proof. intro. split.
  apply plug_BopL_equiv'. apply H.
  apply plug_BopL_equiv'. apply H.
Qed.

Lemma plug_BopR_equiv' (b : bop) (e e1 e2 : expr) (s : state Z)
  (H : forall n : Z, [|e1|] s => n -> [|e2|] s => n) :
  forall n : Z, [|Bop b e e1|] s => n -> [|Bop b e e2|] s => n.
Proof. intros. inversion H0.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  econstructor. exact VALA. exact (H zb VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
Qed.

Lemma plug_BopR_equiv (b : bop) (e e1 e2 : expr) (s : state Z)
  (H : forall n : Z, [|e1|] s => n <-> [|e2|] s => n) :
  forall n : Z, [|Bop b e e1|] s => n <-> [|Bop b e e2|] s => n.
Proof. intro. split.
  apply plug_BopR_equiv'. apply H.
  apply plug_BopR_equiv'. apply H.
Qed.

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof. split.
  intro. intro. induction C.
    exact H.
    intro. intro. apply plug_BopL_equiv. exact (fun n => IHC n s).
    intro. intro. apply plug_BopR_equiv. exact (fun n => IHC n s).
  intro. exact (H Hole).
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

  Reserved Notation "st |- e -->> e'" (at level 0).

  Inductive ss_eval : state Z -> expr -> expr -> Prop :=
    se_Stop : forall (s : state Z)
                     (z : Z),  s |- (Nat z) -->> (Nat z)
  | se_Step : forall (s : state Z)
                     (e e' e'' : expr)
                     (HStep : s |- e --> e')
                     (Heval: s |- e' -->> e''), s |- e -->> e''
  where "st |- e -->> e'"  := (ss_eval st e e').
  
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof. intro. intro. inversion HV. subst. destruct H. inversion H. Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. intro. remember (Nat 0 [/] Nat 0).
    assert (normal_form e). intro. intro. destruct H0. subst. inversion H0.
      inversion LEFT.
      inversion RIGHT.
      inversion EVAL. inversion VALB. subst. contradiction.
    remember (H e H0). inversion i. subst. inversion H1.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. intro. remember (H
    ((Nat 1 [+] Nat 2) [*] (Nat 3 [+] Nat 4))
    (Nat (1 + 2) [*] (Nat 3 [+] Nat 4))
    ((Nat 1 [+] Nat 2) [*] Nat (3 + 4))
    []).
    assert ((Nat (1 + 2) [*] (Nat 3 [+] Nat 4)) <> (Nat 1 [+] Nat 2) [*] Nat (3 + 4)). intro. inversion H0.
    apply H0. apply e.
      apply ss_Left.  apply ss_Bop. apply bs_Add. apply bs_Nat. apply bs_Nat.
      apply ss_Right. apply ss_Bop. apply bs_Add. apply bs_Nat. apply bs_Nat.
  Qed.

  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. inversion H1.
    subst. inversion H2.
      subst. assert (z0 = z).
        apply (state_deterministic Z s i). exact VAL0. exact VAL.
        subst. reflexivity.
    subst. inversion H2.
      inversion LEFT.
      inversion RIGHT.
      subst. assert (z0 = z).
        remember (Bop op (Nat zl) (Nat zr)). apply (eval_deterministic e s). exact EVAL0. exact EVAL.
        subst. reflexivity.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. induction Heval. apply isv_Intro. exact IHHeval. Qed.
  
  Lemma ss_bs_correct (e e' : expr) (s : state Z) (z : Z) (BS : [|e|] s => z) (SS : s |- e --> e') : [|e'|] s => z.
  Proof. generalize z BS. clear BS z. induction SS; intros.
    inversion BS. subst. assert (z = z0). apply state_deterministic with s i. exact VAL. exact VAR. subst. apply bs_Nat.
    apply plug_BopL_equiv' with l. exact IHSS. exact BS.
    apply plug_BopR_equiv' with r. exact IHSS. exact BS.
    assert (z = z0). apply eval_deterministic with (Bop op (Nat zl) (Nat zr)) s. exact EVAL. exact BS. subst. apply bs_Nat.
  Qed.

  (*Lemma ss_bop_concatenation (e1 e2 : expr) (s : state Z) (z z1 z2 : Z) (b : bop)
    (BS1 : [|e1|] s => z1)
    (BS2 : [|e2|] s => z2)
    (SS1 : s |- e1 -->> (Nat z1))
    (SS2 : s |- e2 -->> (Nat z2))
    (Base : forall za zb, s |- Bop b (Nat za) (Nat zb) -->> (Nat z)) :
    s |- Bop b e1 e2 -->> (Nat z).
  Proof.
    induction SS1; subst.
      induction SS2; subst.
        apply Base.
        apply se_Step with (Bop b (Nat z0) e'). apply ss_Right. exact HStep. apply IHSS2. exact BS1. apply ss_bs_correct with e. exact BS2. exact HStep. exact Base.
      apply se_Step with (Bop b e' e2). apply ss_Left. exact HStep. apply IHSS1. apply ss_bs_correct with e. exact BS1. exact HStep. exact BS2. exact SS2. exact Base.
  Qed.*)

  (*Lemma ss_bs_equiv (e : expr) (s : state Z) (z z' : Z)
    (BS : [|e|] s => z)
    (SS : s |- e --> (Nat z')) :
    z = z'.
  Proof. inversion SS; subst.
    assert ([|Var i|] s => z'). apply bs_Var. exact VAL. apply eval_deterministic with (Var i) s. exact BS. exact H.
    apply eval_deterministic with (Bop op (Nat zl) (Nat zr)) s. exact BS. exact EVAL.
  Qed.*)

  Lemma ss_bs_correct_rev (e e' : expr) (s : state Z) (z : Z) (BS : [|e'|] s => z) (SS : s |- e --> e') : [|e|] s => z.
  Proof. generalize z BS. clear BS z. induction SS; intros.
    inversion BS. subst. apply bs_Var. exact VAL.
    apply plug_BopL_equiv' with l'. exact IHSS. exact BS.
    apply plug_BopR_equiv' with r'. exact IHSS. exact BS.
    inversion BS. subst. exact EVAL.
  Qed.

  Lemma se_BopL_evaluation (l r : expr) (b : bop) (s : state Z) (z : Z)
    (SE : s |- (Bop b l r) -->> (Nat z)) :
    exists z', s |- l -->> (Nat z').
  Proof. remember (Bop b l r). remember (Nat z).
    generalize b l r z Heqe Heqe0. clear Heqe0 Heqe z r l b. induction SE.
      intros. inversion Heqe.
      induction HStep; intros; inversion Heqe; subst; clear Heqe.
        assert (exists z', s |- l' -->> (Nat z')). apply IHSE with b r0 z. reflexivity. reflexivity.
        destruct H. exists x. apply se_Step with l'. exact HStep. exact H.
        apply IHSE with b r' z. reflexivity. reflexivity.
        exists zl. apply se_Stop.
  Qed.

  Lemma se_BopR_evaluation (l r : expr) (b : bop) (s : state Z) (z : Z)
    (SE : s |- (Bop b l r) -->> (Nat z)) :
    exists z', s |- r -->> (Nat z').
  Proof. remember (Bop b l r). remember (Nat z).
    generalize b l r z Heqe Heqe0. clear Heqe0 Heqe z r l b. induction SE.
      intros. inversion Heqe.
      induction HStep; intros; inversion Heqe; subst; clear Heqe.
        apply IHSE with b l' z. reflexivity. reflexivity.
        assert (exists z', s |- r' -->> (Nat z')). apply IHSE with b l0 z. reflexivity. reflexivity.
        destruct H. exists x. apply se_Step with r'. exact HStep. exact H.
        exists zr. apply se_Stop.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. split; intro.
    induction H.
      apply se_Stop.
      apply se_Step with (Nat z). apply ss_Var. exact VAR. apply se_Stop.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat (za + zb)). apply ss_Bop. apply bs_Add. exact H. exact H0. apply se_Stop.
          apply se_Step with (Nat z [+] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [+] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat (za - zb)). apply ss_Bop. apply bs_Sub. exact H. exact H0. apply se_Stop.
          apply se_Step with (Nat z [-] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [-] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat (za * zb)). apply ss_Bop. apply bs_Mul. exact H. exact H0. apply se_Stop.
          apply se_Step with (Nat z [*] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [*] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat (Z.div za zb)). apply ss_Bop. apply bs_Div. exact H. exact H0. exact NZERO. apply se_Stop.
          apply se_Step with (Nat z [/] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [/] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat (Z.modulo za zb)). apply ss_Bop. apply bs_Mod. exact H. exact H0. exact NZERO. apply se_Stop.
          apply se_Step with (Nat z [%] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [%] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.one). apply ss_Bop. apply bs_Le_T with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [<=] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [<=] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.zero). apply ss_Bop. apply bs_Le_F with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [<=] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [<=] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.one). apply ss_Bop. apply bs_Lt_T with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [<] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [<] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.zero). apply ss_Bop. apply bs_Lt_F with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [<] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [<] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.one). apply ss_Bop. apply bs_Ge_T with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [>=] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [>=] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.zero). apply ss_Bop. apply bs_Ge_F with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [>=] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [>=] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.one). apply ss_Bop. apply bs_Gt_T with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [>] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [>] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.zero). apply ss_Bop. apply bs_Gt_F with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [>] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [>] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.one). apply ss_Bop. apply bs_Eq_T with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [==] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [==] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.zero). apply ss_Bop. apply bs_Eq_F with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [==] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [==] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.one). apply ss_Bop. apply bs_Ne_T with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [/=] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [/=] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat Z.zero). apply ss_Bop. apply bs_Ne_F with za zb. exact H. exact H0. exact OP. apply se_Stop.
          apply se_Step with (Nat z [/=] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [/=] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat (za * zb)). apply ss_Bop. apply bs_And. exact H. exact H0. exact BOOLA. exact BOOLB. apply se_Stop.
          apply se_Step with (Nat z [&] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [&] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
      induction IHeval1; subst.
        induction IHeval2; subst.
          apply se_Step with (Nat (zor za zb)). apply ss_Bop. apply bs_Or. exact H. exact H0. exact BOOLA. exact BOOLB. apply se_Stop.
          apply se_Step with (Nat z [\/] e'). apply ss_Right. exact HStep. apply IHIHeval2. exact H. apply ss_bs_correct with e. exact H0. exact HStep.
        apply se_Step with (e' [\/] b). apply ss_Left. exact HStep. apply IHIHeval1. apply ss_bs_correct with e. exact H. exact HStep. exact H0. exact IHeval2.
    remember (Nat z). generalize z Heqe0. clear Heqe0 z. induction H; intros; subst.
      inversion Heqe0. apply bs_Nat.
      generalize z IHss_eval H. clear H IHss_eval z. induction HStep; intros.
        assert ([|Nat z|] s => z0). apply IHss_eval. reflexivity.
        inversion H0. subst. apply bs_Var. exact VAL.
        assert ([|Bop op l' r|] s => z). apply IHss_eval. reflexivity.
        apply plug_BopL_equiv' with l'. intros. apply ss_bs_correct_rev with l'. exact H1. exact HStep. exact H0.
        assert ([|Bop op l r'|] s => z). apply IHss_eval. reflexivity.
        apply plug_BopR_equiv' with r'. intros. apply ss_bs_correct_rev with r'. exact H1. exact HStep. exact H0.
        assert ([|Nat z|] s => z0). apply IHss_eval. reflexivity.
        inversion H0. subst. exact EVAL.
  Qed.

  Lemma ss_to_eval (e : expr)
                    (s : state Z)
                    (z : Z) : (e = Nat z \/ s |- e --> (Nat z)) -> [| e |] s => z.
  Proof. intro. destruct H.
    subst. apply bs_Nat.
    inversion H. apply bs_Var. exact VAL. exact EVAL.
  Qed.

  Lemma eval_not_to_ss : exists (e : expr)
                       (s : state Z)
                       (z : Z), ~([| e |] s => z -> (e = Nat z \/ s |- e --> (Nat z))).
  Proof. remember (Nat 1 [+] Nat 2 [+] Nat 3). exists e, [], (1 + 2 + 3)%Z. intro.
    assert ([|e|] [] => (1 + 2 + 3)). subst. apply bs_Add. apply bs_Add. apply bs_Nat. apply bs_Nat. apply bs_Nat.
    destruct (H H0). subst. inversion H1. subst. inversion H1.
  Qed.
  
End SmallStep.

Module Renaming.
  
  Definition renaming := { f : id -> id | Bijective f }.
  
  Fixpoint rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.
  
  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof. destruct r, b, a. exists (exist Bijective x0 (ex_intro _ x (conj e0 e))).
    intro. simpl. apply e.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. destruct r, b, a. exists (exist Bijective x0 (ex_intro _ x (conj e0 e))).
    intro. simpl. apply e0.
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
  Proof. destruct r, r'. induction e; simpl.
    reflexivity.
    assert (x (x0 i) = i). apply (Hinv i). rewrite H. reflexivity.
    rewrite IHe1. rewrite IHe2. reflexivity.
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
  Proof. destruct r, r'. induction st.
    reflexivity.
    destruct a. simpl. assert (x (x0 i) = i). apply (Hinv i). rewrite H. rewrite IHst. reflexivity.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. intro. intros. destruct BH. destruct H0. rewrite <- (H0 x). rewrite <- (H0 y). rewrite H. reflexivity. Qed.

  Lemma eval_renaming_invariance' (e : expr) (st : state Z) (z : Z) (r : renaming) :
    [| e |] st => z -> [| rename_expr r e |] (rename_state r st) => z.
  Proof. intro. generalize st z r H. clear H r z st. induction e; intros; inversion H; clear H.
    apply bs_Nat.
    apply bs_Var. subst. induction VAR; destruct r.
      apply st_binds_hd.
      apply st_binds_tl; simpl.
        intro. remember (bijective_injective x0 b). assert (id = id'). apply i. exact H0. contradiction.
        exact IHVAR.
    apply bs_Add. apply IHe1. exact VALA. apply IHe2. exact VALB.
    apply bs_Sub. apply IHe1. exact VALA. apply IHe2. exact VALB.
    apply bs_Mul. apply IHe1. exact VALA. apply IHe2. exact VALB.
    apply bs_Div. apply IHe1. exact VALA. apply IHe2. exact VALB. exact NZERO.
    apply bs_Mod. apply IHe1. exact VALA. apply IHe2. exact VALB. exact NZERO.
    apply bs_Le_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Le_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Lt_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Lt_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Ge_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Ge_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Gt_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Gt_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Eq_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Eq_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Ne_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Ne_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_And. apply IHe1. exact VALA. apply IHe2. exact VALB. exact BOOLA. exact BOOLB.
    apply bs_Or. apply IHe1. exact VALA. apply IHe2. exact VALB. exact BOOLA. exact BOOLB.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. split; intro.
    apply eval_renaming_invariance'. exact H.
    destruct (renaming_inv r).
      assert ([|rename_expr x (rename_expr r e)|] (rename_state x (rename_state r st)) => z).
        apply eval_renaming_invariance'. exact H.
      assert (rename_expr x (rename_expr r e) = e).
        apply re_rename_expr. exact H0.
      assert (rename_state x (rename_state r st) = st).
        apply re_rename_state. exact H0.
      rewrite -> H2 in H1. rewrite -> H3 in H1. exact H1.
  Qed.

End Renaming.
