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

  Lemma zero_always x (s : state Z) (v : Z) (EVALH: s / x => v) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof.
    remember (bs_Var s x v EVALH) as HVar.
    remember (bs_Nat s 0) as HNat.
    remember (bs_Mul s (Var x) (Nat 0) v Z.zero HVar HNat) as HMul.
    clear HeqHMul.
    rewrite Z.mul_0_r in HMul.
    assumption.
  Qed.
    
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    apply bs_Nat.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH. subst.
    inversion VALB. subst.
    remember (Zplus_diag_eq_mult_2 za) as H2.
    rewrite <- H2.
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
  generalize dependent z.
  induction e.
  - intros. inversion HV. subst. inversion HSub. subst. exists z0. assumption.
  - intros. inversion HV. subst. inversion HSub. subst. exists z. assumption.
  - intros. inversion HV; subst; inversion HSub; subst; eauto.
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
  induction e; intros.
    - inversion ID.
    - inversion RED. subst. inversion ID. subst. 
      exists z. assumption.
    - inversion RED; subst; inversion_clear ID; subst; destruct H.
      all: try (apply IHe1 with za; assumption).
      all: try (apply IHe2 with zb; assumption).
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z H.
  remember (defined_expression e s z id H ID) as HDef.
  inversion HDef.
  specialize (UNDEF x).
  auto.
Qed.


(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  revert z1 z2 E1 E2.
  induction e; intros.
  - inversion E1; inversion E2; subst; reflexivity.
  - inversion E1; inversion E2; subst.
    apply (state_deterministic Z s i z1 z2); assumption.
  - intros.
    inversion E1; 
    inversion E2;
    subst;
    remember (IHe1 za za0 VALA VALA0); 
    remember (IHe2 zb zb0 VALB VALB0);
    subst;
    try (reflexivity);
    try (contradiction);
    try (congruence).
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
  (* generalize dependent s2.  *)
  generalize dependent z.
  induction e; intros.
  - inversion EV; subst.
    apply SmokeTest.nat_always. 
  - inversion EV; subst.
    apply bs_Var.
    apply FV.
    + apply v_Var.
    + assumption.
  - inversion EV; subst;
    apply IHe1 in VALA;
    apply IHe2 in VALB;
    subst;
    eauto. 
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
  unfold equivalent in *.
  symmetry in EQ.
  assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in *.
  intros.
  specialize (EQ1 n s).
  specialize (EQ2 n s).
  rewrite EQ1.
  assumption.
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
  - split; intros.
    all: generalize dependent n; induction C; intros.
    all: try (apply H; assumption).
    all:
      inversion H0; subst;
      try (apply IHC in VALA); try (apply IHC in VALB);
      econstructor; eauto.
  - split; intros; apply (H Hole); assumption.
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
    induction HE; auto.
    apply (reach_step s e e' e''); auto.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z).
    induction HR; subst; eauto.
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
    - apply se_Step with e'; eauto.
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
    intros s H.
    inversion H.
    inversion H0.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intros H.
    remember ((Nat 1) [/] (Nat 0)) as e.
    specialize (H e).
    assert (HNF : normal_form e).
    { subst. unfold normal_form.
      intros s H0.
      inversion H0; subst.
      inversion H1; subst.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL; subst.
        inversion VALB; subst.
        apply NZERO.
        reflexivity. }
    apply H in HNF.
    inversion HNF; subst.
    inversion H0.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    intros H.
    remember ((Var (Id 0)) [+] (Var (Id 1))) as e.
    remember ((Nat 1) [+] (Var (Id 1))) as e'.
    remember ((Var (Id 0)) [+] (Nat 1)) as e''.
    remember ([(Id 0, 1%Z); (Id 1, 1%Z)]) as s.
    specialize (H e e' e'' s).
    assert (H1 : s |- e --> e').
    { subst. apply ss_Left. apply ss_Var. apply st_binds_hd. }
    assert (H2 : s |- e --> e'').
    { subst. apply ss_Right. apply ss_Var. apply st_binds_tl.
      remember (id_eq_dec (Id 1) (Id 0)) as Hneq.
      inversion Hneq. inversion H0. assumption.
      apply st_binds_hd. }
    specialize (H H1 H2).
    subst.
    inversion Heqe''.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst.
    - inversion H2; subst.
      rewrite (state_deterministic Z s i z z0); auto.
    - inversion H2; subst.
      + inversion LEFT.
      + inversion RIGHT.
      + remember (Bop op (Nat zl) (Nat zr)) as e.
        rewrite (eval_deterministic e s z z0); auto.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval; subst.
    - apply isv_Intro.
    - assumption.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction C.
    - assumption.
    - simpl.
      induction IHC; auto.
      apply reach_step with (Bop b e'0 e0).
      apply ss_Left; assumption.
      assumption.
    - simpl.
      induction IHC; auto.
      apply reach_step with (Bop b e0 e'0).
      apply ss_Right; assumption.
      assumption.
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    remember (Bop op e1' e2) as mid.
    apply ss_reachable_trans with mid.
    - apply ss_subst with (C := BopL op Hole e2) in HR1.
      subst.
      assumption.
    - apply ss_subst with (C := BopR op e1' Hole) in HR2.
      subst.
      assumption.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    inversion H; subst;
    rewrite (eval_deterministic e1 s za za0 VALA VALA0);
    rewrite (eval_deterministic e2 s zb zb0 VALB VALB0);
    eauto.
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
    apply ss_eval_reachable in IHe1.
    apply ss_eval_reachable in IHe2.
    apply ss_reachable_trans with (Bop op (Nat za) (Nat zb)).
    - apply ss_subst_binop; auto.
    - apply ss_bop_reachable with e1 e2; auto.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    split.
    - intros; induction H; eauto.
    - intros.
      generalize dependent z.
      induction e.
      + intros.
        inversion H; subst.
        * auto.
        * inversion HStep.
      + intros.
        inversion H; subst.
        inversion HStep; subst.
        inversion Heval; subst.
        * auto.
        * inversion HStep0.
      + intros.
        assert (exists zl zr, s |- e1 -->> (Nat zl) /\ s |- e2 -->> (Nat zr) /\ [|Bop b (Nat zl) (Nat zr)|] s => z).
        { clear IHe1 IHe2.
          remember (Bop b e1 e2).
          remember (Nat z).
          generalize dependent e2.
          generalize dependent e1.
          induction H; intros. inversion Heqe.
          specialize (IHss_eval Heqe0).
          inversion HStep; subst.
          - inversion H1.
          - specialize (IHss_eval l' e2).
            inversion H1; subst.
            assert (Bop b l' e2 = Bop b l' e2) by reflexivity.
            specialize (IHss_eval H0).
            destruct IHss_eval as [zl [zr [R1 [R2 R3]]]].
            exists zl, zr.
            eauto.
          - specialize (IHss_eval e1 r').
            inversion H1; subst.
            assert (Bop b e1 r' = Bop b e1 r') by reflexivity.
            specialize (IHss_eval H0).
            destruct IHss_eval as [zl [zr [R1 [R2 R3]]]].
            exists zl, zr.
            eauto.
          - inversion H1; subst.
            exists zl, zr.
            split. try (apply se_Stop).
            split. try (apply se_Stop).
            inversion H; subst.
            + assumption.
            + inversion HStep0.
        }
        destruct H0 as [zl [zr [H1 [H2 H3]]]].
        specialize (IHe1 zl H1).
        specialize (IHe2 zr H2).
        inversion H3; inversion VALA; inversion VALB; subst; eauto.
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
    inversion H1; inversion H2; subst; auto.
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
  Proof.
    intros.
    generalize dependent t'.
    induction HR.
    - intros.
      inversion HS; inversion HT. 
      all: try (subst; eauto).
  Abort.


  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    intros.
    inversion HT; inversion HVal; subst.
    all: try (inversion H0; subst; unfold zbool; eauto).
    all: try (inversion BOOLA; inversion BOOLB; subst; eauto).
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
    destruct r as [f BH].
    destruct BH as [f' [Hbij Hinv]].
    assert (BH': Bijective f').
    { unfold Bijective. exists f. auto. }
    exists (exist _ f' BH').
    unfold renamings_inv.
    exact Hbij.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [f BH].
    destruct BH as [f' [Hbij Hinv]].
    assert (BH': Bijective f').
    { unfold Bijective. exists f. auto. }
    exists (exist _ f' BH').
    unfold renamings_inv.
    exact Hinv.
  Qed.

  Lemma renaming_inv3 (r : renaming) : exists (r' : renaming), renamings_inv r' r /\ renamings_inv r r'.
  Proof.
    destruct r as [f BH].
    destruct BH as [f' [Hbij Hinv]].
    assert (BH': Bijective f').
    { unfold Bijective. exists f. auto. }
    exists (exist _ f' BH').
    unfold renamings_inv.
    split.
    exact Hbij.
    exact Hinv.
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
    - destruct r as [f BH]; destruct r' as [f' BH']; unfold renamings_inv in Hinv.
      rewrite Hinv.
      reflexivity.
    - rewrite IHe1, IHe2; auto.
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
    induction st; simpl; auto.
    destruct r as [f BH].
    destruct r' as [f' BH'].
    destruct a.
    specialize (Hinv i).
    unfold rename_state in *.
    unfold rename_id in *.
    rewrite IHst.
    rewrite Hinv.
    reflexivity.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    destruct BH as [f' [Hbij Hinv]].
    unfold Injective.
    intros x y Hxy.
    specialize (Hbij x) as Hx.
    specialize (Hbij y) as Hy.
    rewrite Hxy in Hx.
    rewrite Hx in Hy.
    exact Hy.
  Qed.
  
  Lemma rename_simpl (r : renaming) (st : state Z) (i : id) (x : Z) :
    rename_state r ((i, x) :: st) = (rename_id r i, x) :: rename_state r st.
  Proof.
    destruct r as [f BH].
    unfold rename_state.
    unfold rename_id.
    reflexivity.
  Qed.

  Lemma rename_equiv' (r : renaming) (st : state Z) (x : id) (z : Z) :
    st / x => z -> (rename_state r st) / rename_id r x => z.
  Proof.
    intros.
    induction H.
    - rewrite rename_simpl.
      apply st_binds_hd.
    - rewrite rename_simpl.
      apply st_binds_tl.
      + destruct r as [f [f' [Hbij Hinv]]].
        unfold rename_id.
        congruence.
      + assumption.
  Qed.

  Lemma rename_equiv (r : renaming) (st : state Z) (x : id) (z : Z) :
    st / x => z <-> (rename_state r st) / rename_id r x => z.
  Proof.
    split; intros.
      - apply rename_equiv'; auto.
      - pose proof (renaming_inv3 r) as [r' [Hinv Hinv']].
        rewrite <- (re_rename_state r' r Hinv st) in *.
        rewrite (re_rename_state r r' Hinv' (rename_state r st)) in H.
        rewrite <- (Hinv x) in *.
        rewrite (Hinv' (rename_id r x)) in H.
        apply (rename_equiv' r' (rename_state r st)).
        assumption.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    split.
    - intros H. induction H; econstructor; eauto.
      apply rename_equiv.
      assumption.
    - intros H.
      remember (rename_state r st) as st'.
      remember (rename_expr r e) as e'.
      generalize dependent z.
      generalize dependent e'.
      generalize dependent st'.
      induction e; intros.
      + subst; simpl in *; inversion H; subst; auto.
      + subst; simpl in *; inversion H; subst. apply rename_equiv in VAR. auto.
      + specialize (IHe1 st' Heqst' (rename_expr r e1)).
        assert (rename_expr r e1 = rename_expr r e1) by reflexivity.
        specialize (IHe1 H0).
        specialize (IHe2 st' Heqst' (rename_expr r e2)).
        assert (rename_expr r e2 = rename_expr r e2) by reflexivity.
        specialize (IHe2 H1).  
        assert (e' = Bop b (rename_expr r e1) (rename_expr r e2)).
        { unfold rename_expr in *. exact Heqe'. }
        rewrite H2 in H.
        inversion H; subst; eauto.
  Qed.
End Renaming.
