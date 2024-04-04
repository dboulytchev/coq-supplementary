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
  Proof.
    apply bs_Nat.  
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. 
    inversion HH. inversion VALB.
    replace (za * 2)%Z with (za + za)%Z.
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
Proof. revert HSub. revert e'. revert HV. revert z.
induction e; intros.
  - inversion HSub. econstructor. eassumption.
  - inversion HSub. econstructor. eassumption.
  - inversion HV.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
       inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
       inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
      inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
      inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
      + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
      inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
      inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
        inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
    + specialize (IHe1 za VALA).
      specialize (IHe2 zb VALB).
      inversion HSub.
        * econstructor. eassumption.
        * specialize (IHe1 e' H6). assumption.
        * specialize (IHe2 e' H6). assumption.
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
  induction RED.
    + inversion ID.
    + inversion ID. rewrite <- H1.
      econstructor. eassumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.      
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. intros. intuition.
  remember (defined_expression e s z id H ID). 
  destruct e0. remember (UNDEF x s0). contradiction.  
Qed.

(* The evaluation relation is deterministic *)

Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  revert E1. revert E2. revert z1. revert z2. 
  induction e ; intros.
    - inversion E1. inversion E2. rewrite <- H2. assumption.
    - inversion E1. inversion E2. 
      apply (state_deterministic Z s i z1 z2 VAR VAR0).
    - inversion E1; subst b; inversion E2. 
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          rewrite -> e. rewrite -> e0. 
          reflexivity.  
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          rewrite -> e. rewrite -> e0. 
          reflexivity.  
        + reflexivity.  
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.  
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. contradiction.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. contradiction.
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. contradiction.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. contradiction.
        + reflexivity.        
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. reflexivity.
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
  revert EV. revert z. induction e; intros.
    - inversion EV. apply bs_Nat.
    - inversion EV. remember (v_Var i).
      remember (FV i v). 
      remember (e z). destruct i1.
      remember (s0 VAR).
      apply (bs_Var). assumption.
    - assert ((forall id : id, (id) ? (e1) -> equivalent_states s1 s2 id)).
      { intros.
        assert ((id) ? (Bop b e1 e2)) as IDDF.
        { constructor. auto. }
        specialize (FV id IDDF).
        assumption. }
      specialize (IHe1 H).
      assert ((forall id : id, (id) ? (e2) -> equivalent_states s1 s2 id)).
      { intros.
        assert ((id) ? (Bop b e1 e2)) as IDDF.
        { constructor. auto. }
        specialize (FV id IDDF).
        assumption. }
      specialize (IHe2 H0).
      inversion EV;
      specialize (IHe1 za VALA); specialize (IHe2 zb VALB);
      econstructor; eassumption.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. constructor. 
  - auto.
  - auto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. constructor; remember (EQ n s); destruct i; assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  constructor; remember (EQ1 n s); remember (EQ2 n s);
  destruct i; destruct i0; auto.
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
  constructor; intros.
  - constructor.
    + revert H. revert n.
      induction C.
      * intros. simpl. simpl in H0.
        specialize (H n s). destruct H. apply (H H0).
      * intros. simpl. simpl in H0.
        inversion H0; econstructor;
            specialize (IHC za H VALA);
            eassumption;
            assumption.
      * intros. simpl. simpl in H0.
        inversion H0.
          -- constructor. assumption. apply (IHC zb H VALB).
          -- constructor. assumption. apply (IHC zb H VALB).
          -- constructor. assumption. apply (IHC zb H VALB).
          -- constructor. assumption. apply (IHC zb H VALB). assumption.
          -- constructor. assumption. apply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption. assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption. assumption.
    + revert H. revert n. induction C.
      * intros. simpl. simpl in H0.
        specialize (H n s). destruct H. apply (H1 H0).
      * intros. simpl. simpl in H0.
        inversion H0; econstructor;
            specialize (IHC za H VALA);
            eassumption;
            assumption.
      * intros. simpl. simpl in H0.
        inversion H0.
          -- constructor. assumption. apply (IHC zb H VALB).
          -- constructor. assumption. apply (IHC zb H VALB).
          -- constructor. assumption. apply (IHC zb H VALB).
          -- constructor. assumption. apply (IHC zb H VALB). assumption.
          -- constructor. assumption. apply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption. assumption.
          -- econstructor. eassumption. eapply (IHC zb H VALB). assumption. assumption.
  -  specialize (H (Hole)). simpl in H. assumption.
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
  Proof.  
    unfold normal_form. 
    intros. intuition.
    destruct H.
    inversion HV. subst e.
    inversion H.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intuition.
    assert (~(is_value ((Nat 1) [/] (Nat 0)))).
    { intuition. inversion H0. }
    assert (normal_form ((Nat 1) [/] (Nat 0))).
    { unfold normal_form. intuition. inversion H1.
      inversion H2. 
      + inversion LEFT.
      + inversion RIGHT.
      + inversion EVAL. inversion VALB.
        subst zb. contradiction.
    }
    auto. 
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    remember (Bop Add (Bop Add (Nat 1) (Nat 1)) (Bop Add (Nat 1) (Nat 1))) as S.
    remember (Bop Add (Nat 2) (Bop Add (Nat 1) (Nat 1))) as L.
    remember (Bop Add (Bop Add (Nat 1) (Nat 1)) (Nat 2)) as R.

    assert ([] |- S --> L).
    { 
      subst S. subst L. apply ss_Left. apply ss_Bop. replace (2)%Z with ((1) + (1))%Z.
      - apply bs_Add. auto. auto.
      - lia.  
    }
    assert ([] |- S --> R).
    { 
      subst S. subst R. apply ss_Right. apply ss_Bop. replace (2)%Z with ((1) + (1))%Z.
      - apply bs_Add. auto. auto.
      - lia.  
    }
    intuition.
    remember (H1 S L R ([]) H H0). 
    subst R. subst L. discriminate e.  
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1. 
      - subst e. inversion H2.
        remember (state_deterministic Z s i z z1 VAL VAL0).
        rewrite <- e. reflexivity.
      - subst e. inversion H2. 
        + remember (isv_Intro zl).
          remember (value_is_normal_form (Nat zl) i s).
          assert (exists e' : expr,
          (s) |- Nat zl --> (e')).
          {
            econstructor. eassumption.
          } contradiction.  
        + remember (isv_Intro zr).
          remember (value_is_normal_form (Nat zr) i s).
          assert (exists e' : expr,
          (s) |- Nat zr --> (e')).
          {
            econstructor. eassumption.
          } contradiction.  
        + remember (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z1 EVAL EVAL0).
          rewrite <- e. reflexivity.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    + apply isv_Intro.
    + assumption. 
  Qed.

  Lemma ss_count_children (s       : state Z)
                     (zl zr z : Z)
                     (e1 e2 : expr)
                     (op      : bop)
                     (EVALL :  s |- e1 -->> (Nat zl)) 
                     (EVALR :  s |- e2 -->> (Nat zr))
                     (EVAL : [| Bop op (Nat zl) (Nat zr) |] s => z) :
    s |- (Bop op e1 e2) -->> (Nat z).
  Proof.
    induction EVALL.
    - induction EVALR.
      + eapply se_Step. apply ss_Bop. eassumption. apply se_Stop.
      + eapply se_Step. apply ss_Right. eassumption.
        apply IHEVALR. assumption.
    - eapply se_Step. eapply ss_Left. eassumption.
      apply IHEVALL. assumption. assumption. 
  Qed.

  Lemma ss_strictness (s       : state Z)
      
  (z: Z)
                     (e1 e2 : expr)
                     (op      : bop)
                     (EVAL : s |- (Bop op e1 e2)  -->> (Nat z)) :
    exists (za zb : Z) , s |- e1 -->> (Nat za) /\ s |- e2 -->> (Nat zb) /\ [| Bop op (Nat za) (Nat zb) |] s => z.
  Proof.
    dependent induction EVAL.
    inversion HStep.
    - assert (e' = Bop op l' e2). { auto. }
      assert (Nat z = Nat z). { reflexivity. }
      specialize (IHEVAL z l' e2 op H4 H5).
      destruct IHEVAL. destruct H6.
      destruct H6. destruct H7. subst e1.
      econstructor. econstructor.
      split. 
      + eapply se_Step. eassumption. eassumption.
      + split.
        * eassumption.
         * assumption.
    - assert (e' = Bop op e1 r'). { auto. }
      assert (Nat z = Nat z). { reflexivity. }
      specialize (IHEVAL z e1 r' op H4 H5).
      destruct IHEVAL. destruct H6.
      destruct H6. destruct H7. 
      econstructor. econstructor.
      split.
      + eassumption.
      + split.
        * eapply se_Step. eassumption.
          eassumption.
        * assumption.
    - econstructor. econstructor.
      split.
      + apply se_Stop.
      + split. 
        * apply se_Stop.
        * subst e1. subst e2. inversion HStep.
          -- inversion LEFT.
          -- inversion RIGHT.
          -- subst e'. inversion EVAL. 
            ++ subst z. assumption. 
            ++ inversion HStep0.
  Qed.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. 
    split. revert z.
    - induction e;intros.
      + inversion H. apply se_Stop.
      + inversion H. eapply se_Step.
        * econstructor. inversion H. eassumption. 
        * apply se_Stop.
      + inversion H.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          constructor. apply bs_Nat. apply bs_Nat.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          constructor. apply bs_Nat. apply bs_Nat.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          constructor. apply bs_Nat. apply bs_Nat.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          constructor. apply bs_Nat. apply bs_Nat. assumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          constructor. apply bs_Nat. apply bs_Nat. assumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. assumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption. eassumption.
        * specialize (IHe1 za VALA). specialize (IHe2 zb VALB).
          eapply ss_count_children. eassumption. eassumption. 
          econstructor. apply bs_Nat. apply bs_Nat. eassumption. eassumption.
    - revert z. induction e; intros.
      + inversion H. apply bs_Nat.
        inversion HStep.
      + inversion H. inversion HStep. subst e'. 
        inversion Heval.
        * subst z. apply bs_Var. assumption.
        * inversion HStep0.
      + specialize (ss_strictness s z e1 e2 b H). intros.
        inversion H0. inversion H1. inversion H2. inversion H4.
        specialize (IHe1 x H3). specialize (IHe2 x0 H5).
        inversion H6; inversion VALA; inversion VALB;
          subst za; subst zb;
          econstructor; repeat eassumption. 
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
  Proof. admit. Admitted.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. admit. Admitted.

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
  Proof. admit. Admitted.     

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
    unfold Injective. unfold Bijective in BH. destruct BH as [g H].
    intros. 
    destruct H. remember (H x). remember (H y). clear Heqe0.
    rewrite <- H0 in e0. transitivity (g (f x)). auto. auto.
  Qed.

  Lemma renamed_state_read_rtl (r : renaming) 
                                      (st : state Z) 
                                      (i : id)
                                      (z : Z) :
      ((st) / i => z) <-> ((rename_state r st) / rename_id r i => z).
  Proof.
    split. 
    - intros. induction H; simpl; destruct r eqn:H1; rewrite <- H1.
      + replace (rename_id r id) with (x0 id).
        apply st_binds_hd. unfold rename_id. subst r.
        reflexivity.   
      + replace (rename_id r id) with (x0 id).
        apply st_binds_tl.
        * intuition. remember (bijective_injective x0 b).
          unfold Injective in i. clear Heqi. 
          specialize (i id id' H2). auto.
        * rewrite <- H1 in IHst_binds.
          replace (x0 id) with (rename_id r id).
          assumption. 
          unfold rename_id. subst r. reflexivity.
        *  unfold rename_id. subst r. reflexivity.
    - intros. induction st.
      inversion H.
      destruct a. 
      specialize (id_eq_dec i0 i). intros s. destruct s. 
      + subst i0. simpl in H. destruct r eqn:R. 
        inversion H.
        * simpl in H. 
          rewrite <- R in H. 
          inversion H. apply st_binds_hd. contradiction.
        * simpl in H5. contradiction. 
      + simpl in H. simpl in IHst.
        inversion H.
        * unfold rename_id in H0. destruct r eqn:R. rewrite <- R in H. rewrite <- R in IHst.
          rewrite <- R in H1.
          injection H1 as H1'.
          subst id. remember (bijective_injective x0 b).
          unfold Injective in i1.
          clear Heqi1.
          specialize (i1 i0 i H0).
          subst i. contradiction.
        * apply st_binds_tl. auto.
          inversion H. 
          unfold rename_id in H5.
          destruct r eqn:R. rewrite <- R in H.
          rewrite <- R in H0. rewrite <- R in IHst.
          rewrite <- R in H1. 
          rewrite <- R in H2.
          rewrite <- R in H3. 
          rewrite <- R in H6.
          injection H6. intros.
          subst id0.
          remember (bijective_injective x1 b).
          unfold Injective in i1.
          clear Heqi1.
          specialize (i1 i i0 H10).
          subst i. contradiction.
          destruct r eqn:R.
          rewrite <- R in H0.
          rewrite <- R in H.
          rewrite <- R in IHst.
          apply IHst.
          injection H0. intros.
          subst st0. rewrite <- R in H2. assumption.
  Qed.
  

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. revert z. induction e; intros.
  - simpl. split; intros; inversion H; apply bs_Nat.
  - simpl. split.
    + intros. simpl. inversion H.
      apply bs_Var. apply renamed_state_read_rtl. assumption.
    + intros. inversion H. apply bs_Var. 
      destruct (renamed_state_read_rtl r st i z).
      apply H4. assumption.
  - split; intros.
    + inversion H; simpl; 
      destruct (IHe1 za) as [TOA FROMA];
      destruct (IHe2 zb) as [TOB FROMB].

      all: econstructor.
      all: try apply (TOA VALA).
      all: try apply (TOB VALB).
      all: assumption.
    + inversion H; simpl; 
      destruct (IHe1 za) as [TOA FROMA];
      destruct (IHe2 zb) as [TOB FROMB].

      all: econstructor.
      all: try apply (FROMA VALA).
      all: try apply (FROMB VALB).
      all: assumption.
Qed.

End Renaming.
