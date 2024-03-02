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
  Proof.
    inversion HH.
    inversion VALB.
    assert (G': Z.mul za 2 = Z.add za za).
    lia.
    rewrite G'.
    apply (bs_Add s e e za za).
    apply VALA.
    apply VALA.
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
  generalize dependent z.
  induction e.
  {
    intros.
    inversion HSub.
    exists z0.
    apply HV.
  }
  {
    intros.
    inversion HSub.
    exists z.
    apply HV.
  }
  intros.
  inversion HSub.
  {
    exists z.
    apply HV.
  }
  {
    inversion HV.
    all: apply (IHe1 H1 za); apply VALA.
  }
  {
    inversion HV.
    all: apply (IHe2 H1 zb); apply VALB.
  }
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
Proof.
  generalize dependent z.
  induction e.
  { inversion ID. }
  {
    inversion ID.
    intros.
    inversion RED.
    exists z.
    apply VAR.
  }
  inversion ID.
  inversion H3.
  {
    intros.
    assert (G': exists z1, [| e1 |] s => z1).
    eapply strictness.
    apply subexpr_left.
    apply subexpr_refl.
    apply RED.
    destruct G'.
    apply (IHe1 H4 x).
    apply H5.
  }
  {
    intros.
    assert (G': exists z2, [| e2 |] s => z2).
    eapply strictness.
    apply subexpr_right.
    apply subexpr_refl.
    apply RED.
    destruct G'.
    apply (IHe2 H4 x).
    apply H5.
  }
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  unfold not.
  induction e.
  { inversion ID. }
  {
    inversion ID.
    intros.
    inversion H.
    apply (UNDEF z).
    apply VAR.
  }
  intros.
  inversion ID.
  inversion H4.
  {
    assert (G': exists z, [| e1 |] s => z).
    eapply strictness.
    apply subexpr_left.
    apply subexpr_refl.
    apply H.
    destruct G'.
    apply (IHe1 H5 x).
    apply H6.
  }
  {
    assert (G': exists z, [| e2 |] s => z).
    eapply strictness.
    apply subexpr_right.
    apply subexpr_refl.
    apply H.
    destruct G'.
    apply (IHe2 H5 x).
    apply H6.
  }
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z)
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z2.
  generalize dependent z1.
  induction e.
  {
    intros.
    inversion E1.
    inversion E2.
    rewrite <- H2.
    rewrite <- H5.
    reflexivity.
  }
  {
    intros.
    inversion E1.
    inversion E2.
    eapply (state_deterministic Z s i).
    apply VAR.
    apply VAR0.
  }
  intros.

  destruct b.

  all: try by
    inversion E1;
    inversion E2;
    rewrite (IHe1 za VALA za0 VALA0);
    rewrite (IHe2 zb VALB zb0 VALB0);
    reflexivity.
  all:
    inversion E1;
    [ inversion E2;
      [ reflexivity
      | rewrite (IHe1 za VALA za0 VALA0) in OP;
        rewrite (IHe2 zb VALB zb0 VALB0) in OP;
        contradiction
      ]
    | inversion E2;
      [ rewrite (IHe1 za VALA za0 VALA0) in OP;
        rewrite (IHe2 zb VALB zb0 VALB0) in OP;
        contradiction
      | reflexivity
      ]
    ].
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 /id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
  generalize dependent z.
  induction e.
  {
    intros.
    inversion EV.
    apply bs_Nat.
  }
  {
    intros.
    inversion EV.
    eapply bs_Var.
    apply (FV i).
    apply v_Var.
    apply VAR.
  }

  assert (Sub1: forall i b e1 e2, i ? e1 -> i ? (Bop b e1 e2)).
  intros.
  apply v_Bop.
  left.
  apply H.

  assert (Sub2: forall i b e1 e2, i ? e2 -> i ? (Bop b e1 e2)).
  intros.
  apply v_Bop.
  right.
  apply H.

  assert (IHe1': forall z, [| e1 |] s1 => z -> [| e1 |] s2 => z).
  intros.
  eapply IHe1.
  intros.
  eapply FV.
  apply Sub1.
  apply ID.
  apply H.

  assert (IHe2': forall z, [| e2 |] s1 => z -> [| e2 |] s2 => z).
  intros.
  eapply IHe2.
  intros.
  eapply FV.
  apply Sub2.
  apply ID.
  apply H.

  intros.
  inversion EV.

  apply bs_Add. apply IHe1'. apply VALA. apply IHe2'. apply VALB.
  apply bs_Sub. apply IHe1'. apply VALA. apply IHe2'. apply VALB.
  apply bs_Mul. apply IHe1'. apply VALA. apply IHe2'. apply VALB.

  apply bs_Div. apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply NZERO.
  apply bs_Mod. apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply NZERO.

  apply (bs_Le_T s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Le_F s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Lt_T s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Lt_F s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Ge_T s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Ge_F s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Gt_T s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Gt_F s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Eq_T s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Eq_F s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Ne_T s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.
  apply (bs_Ne_F s2 e1 e2 za zb). apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply OP.

  apply bs_And. apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply BOOLA. apply BOOLB.
  apply bs_Or. apply IHe1'. apply VALA. apply IHe2'. apply VALB. apply BOOLA. apply BOOLB.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z),
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  split.
  intro.
  apply H.
  intro.
  apply H.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  split.
  intro.
  apply EQ.
  apply H.
  intro.
  apply EQ.
  apply H.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  split.
  intro.
  apply EQ2.
  apply EQ1.
  apply H.
  intro.
  apply EQ1.
  apply EQ2.
  apply H.
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
  intro.
  split.
  {
    generalize dependent n.
    induction C.
    {
      intros.
      apply H.
      apply H0.
    }
    {
      intros.
      simpl in H0.
      simpl.
      inversion H0.
      apply bs_Add. apply IHC. apply VALA. apply VALB.
      apply bs_Sub. apply IHC. apply VALA. apply VALB.
      apply bs_Mul. apply IHC. apply VALA. apply VALB.
      apply bs_Div. apply IHC. apply VALA. apply VALB. apply NZERO.
      apply bs_Mod. apply IHC. apply VALA. apply VALB. apply NZERO.
      apply (bs_Le_T s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Le_F s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Lt_T s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Lt_F s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Ge_T s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Ge_F s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Gt_T s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Gt_F s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Eq_T s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Eq_F s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Ne_T s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Ne_F s (C <~ e2) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply bs_And. apply IHC. apply VALA. apply VALB. apply BOOLA. apply BOOLB.
      apply bs_Or. apply IHC. apply VALA. apply VALB. apply BOOLA. apply BOOLB.
    }
    {
      intros.
      simpl in H0.
      simpl.
      inversion H0.
      apply bs_Add. apply VALA. apply IHC. apply VALB.
      apply bs_Sub. apply VALA. apply IHC. apply VALB.
      apply bs_Mul. apply VALA. apply IHC. apply VALB.
      apply bs_Div. apply VALA. apply IHC. apply VALB. apply NZERO.
      apply bs_Mod. apply VALA. apply IHC. apply VALB. apply NZERO.
      apply (bs_Le_T s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Le_F s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Lt_T s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Lt_F s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Ge_T s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Ge_F s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Gt_T s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Gt_F s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Eq_T s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Eq_F s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Ne_T s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Ne_F s e (C <~ e2) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply bs_And. apply VALA. apply IHC. apply VALB. apply BOOLA. apply BOOLB.
      apply bs_Or. apply VALA. apply IHC. apply VALB. apply BOOLA. apply BOOLB.
    }
  }
  {
    generalize dependent n.
    induction C.
    {
      intros.
      apply H.
      apply H0.
    }
    {
      intros.
      simpl in H0.
      simpl.
      inversion H0.
      apply bs_Add. apply IHC. apply VALA. apply VALB.
      apply bs_Sub. apply IHC. apply VALA. apply VALB.
      apply bs_Mul. apply IHC. apply VALA. apply VALB.
      apply bs_Div. apply IHC. apply VALA. apply VALB. apply NZERO.
      apply bs_Mod. apply IHC. apply VALA. apply VALB. apply NZERO.
      apply (bs_Le_T s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Le_F s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Lt_T s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Lt_F s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Ge_T s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Ge_F s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Gt_T s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Gt_F s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Eq_T s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Eq_F s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Ne_T s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply (bs_Ne_F s (C <~ e1) e za zb). apply IHC. apply VALA. apply VALB. apply OP.
      apply bs_And. apply IHC. apply VALA. apply VALB. apply BOOLA. apply BOOLB.
      apply bs_Or. apply IHC. apply VALA. apply VALB. apply BOOLA. apply BOOLB.
    }
    {
      intros.
      simpl in H0.
      simpl.
      inversion H0.
      apply bs_Add. apply VALA. apply IHC. apply VALB.
      apply bs_Sub. apply VALA. apply IHC. apply VALB.
      apply bs_Mul. apply VALA. apply IHC. apply VALB.
      apply bs_Div. apply VALA. apply IHC. apply VALB. apply NZERO.
      apply bs_Mod. apply VALA. apply IHC. apply VALB. apply NZERO.
      apply (bs_Le_T s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Le_F s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Lt_T s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Lt_F s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Ge_T s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Ge_F s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Gt_T s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Gt_F s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Eq_T s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Eq_F s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Ne_T s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply (bs_Ne_F s e (C <~ e1) za zb). apply VALA. apply IHC. apply VALB. apply OP.
      apply bs_And. apply VALA. apply IHC. apply VALB. apply BOOLA. apply BOOLB.
      apply bs_Or. apply VALA. apply IHC. apply VALB. apply BOOLA. apply BOOLB.
    }
  }
  intro.
  apply (H Hole).
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
  Proof.
    unfold not.
    intros.
    destruct H.
    inversion HV.
    inversion H.
    rewrite <- H2 in H0. discriminate.
    rewrite <- H2 in H0. discriminate.
    rewrite <- H2 in H0. discriminate.
    rewrite <- H2 in H0. discriminate.
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. admit. Admitted.

  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. admit. Admitted.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (e = Nat z \/ s |- e --> (Nat z)).
  Proof. admit. Admitted.

End SmallStep.
