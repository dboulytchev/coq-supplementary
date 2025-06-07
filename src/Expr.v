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

  Lemma no_zero_always : ~ (forall x s, [| Var x [*] Nat 0 |] s => Z.zero).
  Proof.
    unfold not; intros H.
    specialize (H (Id 0) []).
    inversion H; subst; clear H.
    inversion VALA; subst; clear VALA.
    inversion VAR.
  Qed.
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    apply bs_Nat.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH; subst; clear HH.
    inversion VALB; subst; clear VALB.
    replace (za * 2) % Z with (za + za) % Z by lia.
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
  generalize dependent st.
  generalize dependent z.
  induction HSub; intros.
  - eauto.
  - inversion HV; subst; eauto.
  - inversion HV; subst; eauto.
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
  induction RED.
  - inversion ID.
  - inversion ID; subst; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
  - inversion ID; subst; destruct H3; eauto.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z H.
  apply (defined_expression e s z id) in H; auto.
  destruct H as [z' Hz'].
  apply (UNDEF z'); auto.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z)
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z2.
  generalize dependent z1.

  induction e; intros z1 H1 z2 H2.
  - inversion H1; inversion H2; subst; reflexivity.
  - inversion H1; inversion H2; subst.
    eapply state_deterministic; eassumption.
  - inversion H1; subst;
    inversion H2; subst;
    destruct (IHe1 za VALA za0 VALA0) as [];
    destruct (IHe2 zb VALB zb0 VALB0) as [];
    try reflexivity;
    try lia;
    try (apply OP0 in OP; destruct OP);
    try (apply OP in OP0; destruct OP0).
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
  generalize dependent s2.
  induction EV; intros s2 FV_hyp.
  
  (* bs_Nat *)
  - constructor.
  
  (* bs_Var *)
  - constructor.
    apply FV_hyp; [constructor | assumption].
  
  (* All binary operators *)
  - apply bs_Add.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
  
  - apply bs_Sub.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
  
  - apply bs_Mul.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
  
  - apply bs_Div.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Mod.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  (* Comparison operators *)
  - apply bs_Le_T with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Le_F with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Lt_T with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Lt_F with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Ge_T with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Ge_F with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Gt_T with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Gt_F with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Eq_T with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Eq_F with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Ne_T with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_Ne_F with za zb.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
  
  - apply bs_And.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
    + assumption.
  
  - apply bs_Or.
    + apply IHEV1; intros; apply FV_hyp; constructor; left; auto.
    + apply IHEV2; intros; apply FV_hyp; constructor; right; auto.
    + assumption.
    + assumption.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. 
  red. intros. tauto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. 
  red. intros. symmetry. apply EQ.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. 
  red. intros. transitivity ([|e2|] s => n); [apply EQ1 | apply EQ2].
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
  split; unfold contextual_equivalent, equivalent in *.
  - intros H C. 
    induction C; try assumption.
    + split; intros Hstep;
      inversion Hstep; subst;
      econstructor; apply IHC in VALA; eauto.
    + split; intros Hstep;
      inversion Hstep; subst;
      econstructor; apply IHC in VALB; eauto.
  - intros H.
    specialize (H Hole).
    exact H.
Qed.

Module SmallStep.
  Require Import Coq.Program.Equality.

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
    induction HE; [constructor | econstructor; eassumption].
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z) as ez.
    induction HR.
    - subst. apply se_Stop.
    - subst. eapply se_Step.
      + eauto.
      + eauto.
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
    - econstructor.
      + eauto.
      + eauto.
  Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1.
    - exact H2.
    - econstructor.
      + eauto.
      + eauto.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    unfold normal_form, not.
    intros s H.
    destruct H as [e' Hstep].
    inversion HV; subst.
    inversion Hstep.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    unfold not.
    intros H.
    remember ((Nat 1) [/] (Nat 0)) as contr.
    
    assert (Hnf: normal_form contr).
    { unfold normal_form, not.
      intros s Hexists.
      destruct Hexists as [e' Hstep].
      subst contr.
      inversion Hstep; subst.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL; subst.
        inversion VALB; subst.
        apply NZERO.
        reflexivity. }
    
    apply H in Hnf.
    subst contr.
    inversion Hnf.
  Qed.
    
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    unfold not.
    intros H.
    
    (* Use a simple counterexample with variables *)
    specialize H with 
      (e := Var (Id 0) [+] Var (Id 0))
      (e' := Nat 0 [+] Var (Id 0))
      (e'' := Var (Id 0) [+] Nat 0)
      (s := [(Id 0, Z.zero)]).
    
    assert (Hl: [(Id 0, Z.zero)] |- (Var (Id 0) [+] Var (Id 0)) --> (Nat 0 [+] Var (Id 0))).
    { apply ss_Left. 
      apply ss_Var. 
      apply st_binds_hd. }
    
    assert (Hr: [(Id 0, Z.zero)] |- (Var (Id 0) [+] Var (Id 0)) --> (Var (Id 0) [+] Nat 0)).
    { apply ss_Right. 
      apply ss_Var. 
      apply st_binds_hd. }
    
    apply H in Hl.
    - inversion Hl.
    - exact Hr.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                           (s    : state Z)
                           (z z' : Z)
                           (H1   : s |- e --> (Nat z))
                           (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst; inversion H2; subst; try reflexivity.
    - f_equal. 
      eapply state_deterministic; eauto.
    - inversion LEFT.
    - inversion RIGHT.
    - f_equal.
      eapply eval_deterministic; eauto.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - constructor.
    - assumption.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction HR.
    - apply reach_base.
    - apply reach_step with (C <~ e').
      + clear IHHR HR.
        induction C; simpl.
        * assumption.
        * apply ss_Left. apply IHC.
        * apply ss_Right. apply IHC.
      + assumption.
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    eapply (ss_subst s (BopL _ Hole _)) in HR1.
    eapply (ss_subst s (BopR _ _ Hole)) in HR2.
    eapply ss_reachable_trans; eauto.
  Qed.
  
  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    apply reach_step with (Nat z).
    - apply ss_Bop.
      inversion H; subst.
      all: assert (Heq1: za = za0) by (eapply eval_deterministic; eauto).
      all: assert (Heq2: zb = zb0) by (eapply eval_deterministic; eauto).
      all: rewrite Heq1, Heq2.
      all: try match goal with
        | |- eval (_ [+] _) _ _ =>  apply bs_Add; apply bs_Nat
        | |- eval (_ [-] _) _ _ =>  apply bs_Sub; apply bs_Nat
        | |- eval (_ [*] _) _ _ =>  apply bs_Mul; apply bs_Nat
        | |- eval (_ [/] _) _ _ =>  apply bs_Div; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [%] _) _ _ =>  apply bs_Mod; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [<=] _) _ (Z.one)  => apply bs_Le_T with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [<=] _) _ (Z.zero) => apply bs_Le_F with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [<] _) _ (Z.one)  =>  apply bs_Lt_T with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [<] _) _ (Z.zero) =>  apply bs_Lt_F with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [>=] _) _ (Z.one)  =>  apply bs_Ge_T with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [>=] _) _ (Z.zero) =>  apply bs_Ge_F with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [>] _) _ (Z.one)  =>  apply bs_Gt_T with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [>] _) _ (Z.zero) =>  apply bs_Gt_F with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [==] _) _ (Z.one)  =>  apply bs_Eq_T with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [==] _) _ (Z.zero) =>  apply bs_Eq_F with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [/=] _) _ (Z.one)  =>  apply bs_Ne_T with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [/=] _) _ (Z.zero) =>  apply bs_Ne_F with za0 zb0; [apply bs_Nat | apply bs_Nat | assumption]
        | |- eval (_ [&] _) _ _ =>  apply bs_And; [apply bs_Nat | apply bs_Nat | assumption | assumption]
        | |- eval (_ [\/] _) _ _ => apply bs_Or; [apply bs_Nat | apply bs_Nat | assumption | assumption]
        end.
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
    eapply ss_reachable_trans.
    - apply ss_subst_binop; apply ss_eval_reachable; eassumption.
    - eapply ss_bop_reachable; eauto.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

  Lemma step_preserves_evaluation s e e' z
    (STEP : (s) |- e --> e')
    (EVAL : [|e'|] s => z) :
    [|e|] s => (z).
  Proof.
    dependent induction e.
    
    (* Case 1: e is a natural number literal (Nat n) *)
    - inversion STEP.
    
    (* Case 2: e is a variable (Var x) *)
    - inversion STEP. 
      subst. 
      eauto. 
      inversion EVAL. 
      subst. 
      eauto.
    
    (* Case 3: e is a binary operation (Bop b e1 e2) *)
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
    
    (* Forward direction: big-step evaluation implies multi-step small-step evaluation *)
    - intro BIGSTEP_EVAL. 
      generalize dependent z.
      dependent induction e.
      
      + intros result EVAL_NAT_N. 
        inversion EVAL_NAT_N. 
        constructor.
      + intros result EVAL_VAR_X. 
        inversion EVAL_VAR_X. 
        subst. 
        eauto.
      + intros result EVAL_BOP. 
        inversion EVAL_BOP; subst; 
        eauto.
    
    (* Backward direction: multi-step small-step evaluation implies big-step evaluation *)
    - intro MULTISTEP_EVAL. 
      dependent induction MULTISTEP_EVAL.
      + constructor.
      + apply (step_preserves_evaluation s e e' z).
        exact HStep.
        apply IHMULTISTEP_EVAL.
        reflexivity.
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
    destruct t1, t2, t3; auto;
    inversion H1; inversion H2; congruence.
  Qed.


  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof. 
    destruct t1, t2; auto;
    inversion H1; inversion H2; congruence.
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
    (* This lemma is actually unprovable - as shown by the counterexamples *)
  Abort.

  Lemma type_preservation_contra : 
    ~ (forall e t t' st e', t' << t -> e :-: t -> st |- e ~~> e' -> e' :-: t').
  Proof.
    unfold "~". intros H.
    pose (e := Var (Id 0)).
    pose (st := [(Id 0, 3%Z)]).
    assert (HS: Bool << Int) by apply subt_base.
    assert (HT: e :-: Int) by (unfold e; apply type_X).
    specialize (H e Int Bool st e HS HT (reach_base st e)).
    inversion H.
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof. 
    intros.
    remember Bool as zb.
    induction HT; intros; try discriminate; subst.
    all: inversion HVal; subst.
    all: try solve [ left; trivial | right; trivial ].
    * inversion BOOLA; subst; inversion BOOLB; subst.
      - left. reflexivity.
      - right. reflexivity.  
      - right. reflexivity.
      - right. reflexivity.
    * inversion BOOLA; subst; inversion BOOLB; subst.
      - left. reflexivity.
      - left. reflexivity.
      - left. reflexivity.
      - right. reflexivity.
  Qed.

End StaticSemantics.

Module Renaming.
  Require Import Coq.Program.Equality.
  
  Definition renaming := { f : id -> id | Bijective f }.
  
  Fixpoint rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.
  
  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof.
    destruct r as [f [g [e1 e2]]].
    assert (Bijective g). { unfold Bijective. exists f. split; assumption. }
    exists (exist Bijective g H).
    unfold renamings_inv. simpl. assumption.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [f [g [e1 e2]]].
    assert (Bijective g). { unfold Bijective. exists f. split; assumption. }
    exists (exist Bijective g H).
    unfold renamings_inv. simpl. assumption.
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
    - reflexivity.
    - simpl. rewrite Hinv. reflexivity.
    - simpl. rewrite IHe1, IHe2. reflexivity.
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
    - destruct a as [i z].
      destruct r as [f Hf].
      destruct r' as [g Hg].
      simpl. rewrite IHst. rewrite Hinv. reflexivity.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    unfold Injective, Bijective in *.
    intros x y H.
    destruct BH as [g [e1 e2]].
    assert (g (f x) = g (f y)) by (rewrite H; reflexivity).
    rewrite e1, e1 in H0. exact H0.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
  [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. 
    split; intros.
    + dependent induction H; simpl; try by econstructor; try eauto.
      econstructor. 
      dependent induction VAR; simpl; destruct r; simpl; constructor.
      - unfold "<>". intros. apply H. eapply bijective_injective; eassumption.
      - apply IHVAR.
    + dependent induction H; dependent destruction e; dependent destruction x;
      try by econstructor; try eauto.
      econstructor.
      dependent induction VAR; simpl; destruct r; simpl; 
      dependent destruction st; inversion x.
      - simpl in x. dependent destruction p. dependent destruction x. 
        assert (Heq: i0 = i) by (eapply bijective_injective; [exact b | exact x]).
        rewrite Heq. constructor.
      - dependent destruction p. dependent destruction x. constructor.
        * intro Hcontra. apply H. 
          simpl. rewrite Hcontra. reflexivity.
        * eapply IHVAR; reflexivity.
  Qed.

End Renaming.
