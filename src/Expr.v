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

#[export] Hint Constructors eval.

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
  forall z :Z, s1 /id => z <-> s2 / id => z.

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

Lemma plug_BopL_equiv (b : bop) (e e1 e2 : expr) (s : state Z)
  (H : forall n : Z, [|e1|] s => n <-> [|e2|] s => n) :
  forall n : Z, [|Bop b e1 e|] s => n <-> [|Bop b e2 e|] s => n.
Proof. intros. split.
  intro. inversion H0.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj1 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  intro. inversion H0.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact (proj2 (H za) VALA). exact VALB. try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
Qed.

Lemma plug_BopR_equiv (b : bop) (e e1 e2 : expr) (s : state Z)
  (H : forall n : Z, [|e1|] s => n <-> [|e2|] s => n) :
  forall n : Z, [|Bop b e e1|] s => n <-> [|Bop b e e2|] s => n.
Proof. intros. split.
  intro. inversion H0.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj1 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
  intro. inversion H0.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
    econstructor. exact VALA. exact (proj2 (H zb) VALB). try exact NZERO. try exact OP. try exact BOOLA. try exact BOOLB.
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

  Inductive ss_eval : state Z -> expr -> expr -> Prop :=
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
  where "st |- e --> e'" := (ss_eval st e e').

  Lemma no_step_from_value (e : expr) (HV: is_value e) : forall s, ~ exists e', (s |- e --> e').
  Proof. intro. intro. inversion HV. subst. destruct H. inversion H. Qed.

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

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (e = Nat z \/ s |- e --> (Nat z)).
  Proof. admit. Admitted.

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
