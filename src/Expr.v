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

  Lemma zero_always x (s : state Z) (z : Z) (H: s / x => z) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof.
    pose proof (bs_Nat s Z.zero) as HNat.
    pose proof (bs_Var s x z H) as HVar.
    pose proof (bs_Mul s (Var x) (Nat 0) z 0%Z HVar HNat) as HMul.
    rewrite (Z.mul_0_r z) in HMul.
    apply HMul.
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
    pose proof (Zplus_diag_eq_mult_2 za) as H2.
    rewrite <- H2.
    apply bs_Add.
    - exact VALA.
    - exact VALA.
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
  - intros z' e. inversion e. subst. inversion HSub. subst. exists z'. assumption.
  - intros z' e. inversion e. subst. inversion HSub. subst. exists z'. assumption.
  - intros z' e. inversion e. subst.
    all: (inversion HSub; subst; eauto).
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
  intros z H.
  pose proof (defined_expression e s z id H ID) as H1.
  inversion H1 as [z' H2].
  specialize (UNDEF z').
  contradiction.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  revert E1 E2. revert z1 z2. 
  induction e.
  - intros. inversion E1. subst. inversion E2. subst. reflexivity.
  - intros. inversion E1. subst. inversion E2. subst. apply (state_deterministic Z s i z1 z2).
    + assumption.
    + assumption.
  - intros. all: (
      inversion E1; 
      subst; 
      inversion E2; 
      subst; 
      pose proof (IHe1 za za0 VALA VALA0); 
      pose proof (IHe2 zb zb0 VALB VALB0); 
      subst;
      try (reflexivity);
      try (contradiction)
    ).
  Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 / id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
  generalize dependent z.
  induction e.
  - intros. inversion EV. subst. apply bs_Nat.
  - intros. inversion EV. subst. apply bs_Var. apply (FV i).
    + apply v_Var.
    + assumption.
  - intros z EV. inversion EV. subst. 
    all: (econstructor). 
    all: (apply IHe1 in VALA; try(exact VALA); try (assumption)).
    all: try (intros id HV; apply FV; apply v_Bop; left; assumption).
    all: (apply IHe2 in VALB; try (exact VALB); try (assumption)).
    all: try (intros id HV; apply FV; apply v_Bop; right; assumption).
  Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  unfold equivalent. 
  intros n s.
  split.
  - intro H. apply H.
  - intro H. apply H.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent in EQ.
  intros n s.
  split.
  - intro H. apply EQ. apply H.
  - intro H. apply EQ. apply H.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in *.
  intros n s.
  split.
  - intro H. apply EQ2. apply EQ1. apply H.
  - intro H. apply EQ1. apply EQ2. apply H.
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
  unfold contextual_equivalent.
  unfold equivalent.
  split.
  - split.
    + generalize dependent n. induction C.
      * intros n H'. simpl. simpl in H'. apply H in H'. assumption.
      * intros n H'. simpl. simpl in H'. inversion_clear H'.
        all: (apply IHC in VALA).
        all: (econstructor).
        all: try (assumption).
        all: try (apply VALA).
        all: try (apply VALB).
        all: try (assumption).
      * intros n H'. simpl. simpl in H'. inversion_clear H'.
        all: (apply IHC in VALB).
        all: (econstructor).
        all: try (assumption).
        all: try (apply VALA).
        all: try (apply VALB).
        all: try (assumption).
    + generalize dependent n. induction C.
      * intros n H'. simpl. simpl in H'. apply H in H'. assumption.
      * intros n H'. simpl. simpl in H'. inversion_clear H'.
        all: (apply IHC in VALA).
        all: (econstructor).
        all: try (assumption).
        all: try (apply VALA).
        all: try (apply VALB).
        all: try (assumption).
      * intros n H'. simpl. simpl in H'. inversion_clear H'.
        all: (apply IHC in VALB).
        all: (econstructor).
        all: try (assumption).
        all: try (apply VALA).
        all: try (apply VALB).
        all: try (assumption).
  - intros H n s. split.
    + specialize (H Hole n s). simpl in H. apply H.
    + specialize (H Hole n s). simpl in H. apply H.
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
      - pose proof (reach_step s e e' e''). apply H in HStep.
        + exact HStep.
        + exact IHHE.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z).
    induction HR.
      - rewrite Heqe0. apply se_Stop.
      - pose proof (se_Step s e e' e''). apply H in HStep.
        + exact HStep.
        + apply IHHR in Heqe0. exact Heqe0.
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
    - apply se_Step with (s:=s) (e:=e) (e':=e') (e'':=e'').
      + exact HStep.
      + apply IHss_eval in H2. exact H2.
  Qed.

  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1.
    - exact H2.
    - apply reach_step with (e:=e) (e':=e').
      + exact HStep.
      + apply IHss_reachable in H2. exact H2.
  Qed.

  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    unfold normal_form. 
    intros s [e' H].
    inversion HV; subst.
    inversion H.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intros H.
    set (e := Nat 0 [/] Nat 0).
    assert (Hnf: normal_form e).
    {
      unfold normal_form.
      intros s [e' Hstep].
      inversion Hstep.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL. inversion VALB. subst. contradiction.
    }
    apply H in Hnf.
    inversion Hnf.
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. 
    intros H.

    set (e := (Nat 2 [*] Nat 3) [+] (Nat 5 [-] Nat 1)).
    set (e1 := Nat 6 [+] (Nat 5 [-] Nat 1)).
    set (e2 := (Nat 2 [*] Nat 3) [+] Nat 4).
    set (s := [] : state Z).
  
    assert (Hstep1 : s |- e --> e1).
    {
      apply ss_Left.
      apply ss_Bop.
      pose proof (bs_Nat s 2) as HNat1.
      pose proof (bs_Nat s 3) as HNat2.
      pose proof (bs_Mul s (Nat 2) (Nat 3) 2 3) as HMul.
      apply HMul in HNat1. assumption. assumption.
    }
  
    assert (Hstep2 : s |- e --> e2).
    {
      apply ss_Right.
      apply ss_Bop.
      pose proof (bs_Nat s 5) as HNat1.
      pose proof (bs_Nat s 1) as HNat2.
      pose proof (bs_Sub s (Nat 5) (Nat 1) 5 1) as HSub.
      apply HSub in HNat1. assumption. assumption.
    }
  
    specialize (H e e1 e2 s Hstep1 Hstep2).
    discriminate H.
  Qed.

  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst.
    inversion H2; subst.
    - pose proof (state_deterministic Z s i z z0) as H.
      apply H in VAL. subst z. reflexivity. assumption.
    - inversion H2; subst.
      + inversion LEFT.
      + inversion RIGHT.
      + pose proof (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z0).
        apply H in EVAL. subst z. reflexivity. assumption.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - apply isv_Intro.
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
    set (HR1e := BopL op Hole e2).
    pose proof (ss_subst s HR1e) as HR1'.
    apply HR1' in HR1.

    set (HR2e := BopR op e1' Hole).
    pose proof (ss_subst s HR2e) as HR2'.
    apply HR2' in HR2.

    simpl in HR1.
    simpl in HR2.

    pose proof (ss_reachable_trans s (Bop op e1 e2) (Bop op e1' e2) (Bop op e1' e2')) as H.
    apply H.
    - exact HR1.
    - exact HR2.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    inversion H.
    all: (specialize (eval_deterministic e1 s za za0 VALA VALA0)).
    all: (specialize (eval_deterministic e2 s zb zb0 VALB VALB0)).
    all: (simpl).
    all: (intros za' zb').
    all: (rewrite za').
    all: (rewrite zb').
    all: (eauto).
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

    apply ss_reachable_trans with (e:=Bop op e1 e2) (e':=Nat z) (e'':=Nat z).
    - pose proof (ss_bop_reachable s e1 e2 op za zb z) as H1.
      pose proof (ss_subst_binop s e1 e2 (Nat za) (Nat zb) op) as H2.
      apply H1 in H. apply H2 in IHe1.
      pose proof (ss_reachable_trans s (Bop op e1 e2) (Bop op (Nat za) (Nat zb)) (Nat z)) as H3.
      apply H3 in IHe1.
      + exact IHe1.
      + exact H.
      + exact IHe2.
      + exact VALA.
      + exact VALB.
    - apply reach_base.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

  Lemma ss_eval_binop_equiv (e1 e2 : expr) (s : state Z) (z : Z) (op : bop) (H : s |- Bop op e1 e2 -->> (Nat z))
        : exists za zb, s |- e1 -->> (Nat za) /\ s |- e2 -->> (Nat zb) /\ [|Bop op (Nat za) (Nat zb)|] s => z.
  Proof.
    remember (Bop op e1 e2).
    remember (Nat z).
    generalize dependent e1. generalize dependent e2.
    induction H.
    - intros. subst. inversion Heqe.
    - intros. subst. inversion HStep. subst. 
      + assert (Nat z = Nat z). reflexivity. pose proof (IHss_eval H0). specialize (H1 e2 l').
        destruct H1 as [za]. reflexivity.
        destruct H1 as [zb].
        destruct H1 as [HL].
        destruct H1 as [HR].
        exists za. exists zb. apply conj.
        * pose proof (se_Step s e1 l' (Nat za)). apply H2 in LEFT. exact LEFT. exact HL.
        * apply conj.
          -- exact HR.
          -- exact H1.
      + assert (Nat z = Nat z). reflexivity. pose proof (IHss_eval H5). specialize (H6 r' e1).
        destruct H6 as [za]. symmetry in H1. assumption.
        destruct H6 as [zb].
        destruct H6 as [HL].
        destruct H6 as [HR].
        exists za. exists zb.
        pose proof (se_Step s e2 r' (Nat zb)). apply H7 in RIGHT.
        * apply conj.
          -- exact HL.
          -- apply conj.
            ++ exact RIGHT.
            ++ exact H6.
        * exact HR.
      + subst. inversion H. subst.
        * exists zl. exists zr. apply conj.
          -- apply se_Stop.
          -- apply conj.
            ++ apply se_Stop.
            ++ exact EVAL.
        * exists zl. exists zr. inversion HStep0.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    split.
    - intro H. generalize dependent z. induction e.
      + intros z' H. inversion H. subst. apply se_Stop.
      + intros z' H. inversion H. subst. pose proof (ss_Var s i z') as H1. apply H1 in VAR.
        pose proof (se_Step s (Var i) (Nat z') (Nat z')) as H2.
        apply H2. assumption. apply se_Stop.
      + intros z' H. inversion H.
        all: (
          specialize (IHe1 za);
          specialize (IHe2 zb); 
          pose proof (IHe1 VALA) as IHe1';
          pose proof (IHe2 VALB) as IHe2';
          pose proof (ss_eval_binop s e1 e2 za zb z' b) as IHB;
          apply IHB in VALA; subst; assumption; assumption; assumption; assumption; assumption
        ).

    - intro H. generalize dependent z. induction e.
      + intros z' H. inversion H. subst. apply bs_Nat. subst. inversion HStep.
      + intros z' H. inversion H. subst. apply bs_Var. inversion HStep. subst. inversion Heval. subst. assumption. subst. inversion HStep0.
      + intros z' H. 
        apply ss_eval_binop_equiv in H. 
        destruct H as [z1]. destruct H as [z2].
        destruct H as [H1]. destruct H as [H2].
        specialize (IHe1 z1).
        specialize (IHe2 z2).
        apply IHe1 in H1.
        apply IHe2 in H2.
        inversion H.
        all: (inversion VALA; inversion VALB; subst; econstructor).
        all: try (apply H1).
        all: try (apply H2).
        all: try (assumption).
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
  Proof. admit. Admitted.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof. admit. Admitted.
  
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
  Proof. admit. Admitted.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof. admit. Admitted.

End StaticSemantics.

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
  Proof. admit. Admitted.
  
  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. admit. Admitted.
    
End Renaming.
