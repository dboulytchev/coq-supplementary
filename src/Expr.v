Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Import Stdlib.Program.Equality.
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

  (* not true. proof below *)
  Lemma zero_always x (s : state Z) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof. Abort.

  Lemma zero_always_is_wrong: (exists x (s: state Z), ~([| Var x [*] Nat 0 |] s => Z.zero)).
  Proof.
    exists (Id 0); exists [].
    intros H_eval; inversion H_eval; subst; inversion VALA; subst; inversion VAR.
  Qed.
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    constructor.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
      inversion HH; subst.
      inversion VALB; subst.
      replace (za * 2)%Z with (za + za)%Z by lia.
      constructor; assumption.
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
  revert st z HV.
  induction HSub.
  - intros st z HV.
    exists z.
    exact HV.
  - intros st z HV.
    inversion HV; subst; eauto.
  - intros st z HV.
    inversion HV; subst; eauto.
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
  induction RED; simpl; try (inversion ID; subst; eauto).
  all: try 
    (inversion ID; subst;
    match goal with
    | H : _ ? _ \/ _ ? _ |- _ => destruct H end;
    [eapply IHRED1 | eapply IHRED2]; assumption).
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z RED.
  destruct (defined_expression e s z id RED ID) as [v HV].
  specialize (UNDEF v).
  contradiction.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z1. generalize dependent z2.
  induction e; intros.
  - (* num *)
    inversion E1; inversion E2; subst; lia.
  - (* var *)
    inversion E1. inversion E2; apply (state_deterministic Z s i z1 z2); auto.
  - (* bop *)
    destruct b; inversion E1; inversion E2;
    specialize (IHe1 _ VALA _ VALA0); specialize (IHe2 _ VALB _ VALB0);
    subst; solve [contradiction | auto]. 
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
  induction e in s1, s2, z, FV, EV |- *. (*Show.*)
  - (* number *)
    inversion EV; subst; constructor.
  - (* var *)
    inversion EV; subst; constructor; apply FV; auto using v_Var.
  - (* bop *)
    inversion EV; subst; econstructor; eauto;
    try (eapply IHe1; eauto; intros; apply FV; left; auto);
    try (eapply IHe2; eauto; intros; apply FV; right; auto).
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. 
  constructor; auto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent.
  intros n s.
  split.
  - intros H. apply EQ. assumption.
  - intros H. apply EQ. assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent.
  intros n s.
  split.
  - intros H. apply EQ2. apply EQ1. assumption.
  - intros H. apply EQ1. apply EQ2. assumption.
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
  - (* => *)
    intros H C. induction C. simpl. (*Show.*)
    + (* Hole *) exact H.
    + (* BopL *) split; intros Ev; inversion Ev; subst; econstructor; eauto; apply IHC; auto.
    + (* BopR *) split; intros Ev; inversion Ev; subst; econstructor; eauto; apply IHC; auto.
  - (* <= *)
    intros H. apply (H Hole).
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
    - (* stop *) apply reach_base.
    - (* step *) apply reach_step with e'.
      + exact HStep.
      + exact IHHE.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z).
    induction HR.
    - (* base *) subst; constructor.
    - (* step *) apply se_Step with e'.
        + assumption.
        + apply IHHR; assumption.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.
  
  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof.
    induction H1; eauto. inversion H2.
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
    intros s [e' Hstep]; inversion HV; subst; inversion Hstep.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intros H.
    assert (HNF : normal_form (Bop Div (Nat 1) (Nat 0))).
    {
      intros s [e' Hstep].
      inversion Hstep; subst.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL; subst.
        inversion VALB; subst.
        contradiction.
    }
    specialize (H (Bop Div (Nat 1) (Nat 0)) HNF).
    inversion H.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. 
    intros H_det.
    pose (i := Id 0).
    pose (z := 0%Z).
    pose (s := (i, z) :: nil).
    assert (H_val : s / i => z).
    { unfold s, i, z. apply st_binds_hd. }
    pose (e := Bop Add (Var i) (Var i)).
    pose (e':= Bop Add (Nat z) (Var i)).
    pose (e'' := Bop Add (Var i) (Nat z)).
    assert (H_step1 : s |- e --> e').
    { unfold e, e'. apply ss_Left. apply ss_Var. exact H_val. }
    assert (H_step2 : s |- e --> e'').
    { unfold e, e''. apply ss_Right. apply ss_Var. exact H_val. }
    specialize (H_det e e' e'' s H_step1 H_step2).
    unfold e', e'' in H_det.
    inversion H_det.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst. (*Show.*)
    - (* var *) inversion H2; subst; remember (state_deterministic Z s i z z0 VAL VAL0); subst; congruence.
    - (* bop *) inversion H2; subst; [inversion LEFT | inversion RIGHT 
        | remember (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z0 EVAL EVAL0); subst; congruence].
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - apply isv_Intro.   
    - exact IHHeval.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction C; simpl.
    - (* hole *) exact HR.
    - (* bopl *) induction IHC; eauto.
    - (* bopr *) induction IHC; eauto.
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    eapply (ss_reachable_trans s (Bop op e1 e2) (Bop op e1' e2) (Bop op e1' e2')).
    - apply (ss_subst s (BopL op Hole e2)). exact HR1.
    - apply (ss_subst s (BopR op e1' Hole)). exact HR2.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    inversion H; subst;
    rewrite (eval_deterministic e1 s za za0 VALA VALA0); subst;
    rewrite (eval_deterministic e2 s zb zb0 VALB VALB0); subst; 
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
    apply ss_reachable_eval. eapply ss_reachable_trans. (*Show.*)
    - apply ss_subst_binop.
      + apply ss_eval_reachable. exact IHe1.
      + apply ss_eval_reachable. exact IHe2. 
    - eapply ss_bop_reachable.
      + exact H.
      + exact VALA.
      + exact VALB.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

  Lemma ss_step_backward (s : state Z) (e e' : expr) (z : Z) (STEP : s |- e --> e')
  (HV : [| e' |] s => z) : [| e |] s => z.
  Proof.
    generalize dependent z;
    induction STEP; intros w HW; inversion HW; subst; try (econstructor; eauto; fail); assumption.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
        split; intro H.
    - (* => *)
      apply ss_reachable_eval; induction H; eauto.
      all: eapply ss_reachable_trans;
        [apply ss_subst_binop; eauto | eapply reach_step; [apply ss_Bop; econstructor; eauto | apply reach_base]].
    - (* <= *)
      remember (Nat z) as v eqn:Hv.
      generalize dependent z; induction H; intros w Hw.
      + injection Hw as ->. constructor.
      + apply ss_step_backward with (e' := e'); auto.
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
    - inversion H2; subst. constructor.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof.
    inversion H1; subst. reflexivity. inversion H2; subst; lia.
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

  (* not true. proof below *)
  Lemma type_preservation e t t' (HS: t' << t) (HT: e :-: t) : forall st e' (HR: st |- e ~~> e'), e' :-: t'.
  Proof. Abort.

  Theorem type_preservation_is_wrong: 
    ~ (forall e t t' (HS: t' << t) (HT: e :-: t), forall st e' (HR: st |- e ~~> e'), e' :-: t').
  Proof.
    intro H_pres.
    pose (x := Id 0). pose (st := (x, 1%Z) :: nil).
    assert (HT : (Var x) :-: Int) by apply type_X.
    assert (HR : st |- (Var x) ~~> (Nat 1)).
    {
      apply reach_step with (e' := Nat 1).
      - apply ss_Var. apply st_binds_hd.
      - apply reach_base.
    }
    specialize (H_pres (Var x) Int Int (subt_refl Int) HT st (Nat 1) HR).
    inversion H_pres; subst. (*Show.*)
    apply HNbool. unfold zbool. left. reflexivity.
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    remember Bool as t.
    induction HT; intros st ? HVal; try discriminate; try (inversion HVal; subst; unfold zbool; tauto).
    - (* and *)
      inversion HVal; subst; unfold zbool.
      assert (H_za : zbool za) by eauto.
      assert (H_zb : zbool zb) by eauto.
      destruct H_za as [-> | ->]; destruct H_zb as [-> | ->]; simpl; auto.
    - (* or *)
      inversion HVal; subst; unfold zor, zbool.
      destruct (Z_le_gt_dec _ _); auto.
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
    destruct r as [f [g [H_fst H_snd]]]. (*Show.*)
    exists (exist _ g (ex_intro _ f (conj H_snd H_fst))).
    unfold renamings_inv, rename_id.
    exact H_fst.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [f [g [H_fst H_snd]]].
    exists (exist _ g (ex_intro _ f (conj H_snd H_fst))).
    unfold renamings_inv, rename_id.
    exact H_snd.
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
    induction e; simpl.
    - (* num *)
      reflexivity.
    - (* var *)
      unfold rename_id.
      rewrite Hinv. 
      reflexivity.
    - (* bop *)
      rewrite IHe1, IHe2. 
      reflexivity.
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
    - (* [] *)
      reflexivity.
    - (* (id, x) *)
      destruct a. destruct r'. destruct r. simpl.
      unfold renamings_inv, rename_id.
      rewrite Hinv.
      rewrite IHst.
      reflexivity.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    unfold Bijective, Injective.
    destruct BH as [g [H_fst H_snd]].
    intros x y H_eq.
    assert (H_g: g (f x) = g (f y)) by (rewrite H_eq; reflexivity).
    rewrite H_fst in H_g. rewrite H_fst in H_g.
    exact H_g.
  Qed.

  (* helper for next lemma *)
  Lemma st_binds_rename (x: id) (st: state Z) (z: Z) (r: renaming):
    st / x => z -> (rename_state r st) / (rename_id r x) => z.
  Proof.
    intro H.
    induction H.
    - (* hd *) destruct r. apply st_binds_hd.
    - (* tl *)
      destruct r as [f H_f]. simpl. apply st_binds_tl.
      + (*  id != id' *)
        intro H_eq. apply H.
        apply bijective_injective with (f := f); assumption.
      + exact IHst_binds.
  Qed.
  
  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    assert (L : forall (q : renaming) (s : state Z) (x : id) (v : Z) (HB : s / x => v),
      (rename_state q s) / (rename_id q x) => v).
    { intros [f Bf] s x v HB.
      induction HB; simpl.
      - apply st_binds_hd.
      - apply st_binds_tl; [ | exact IHHB ].
        intro Heq. apply H.
        apply (bijective_injective f Bf). exact Heq. }
    assert (FWD : forall (q : renaming) (e0 : expr) (s : state Z) (v : Z) (HV : [| e0 |] s => v),
      [| rename_expr q e0 |] (rename_state q s) => v).
    { intros q e0 s v HV. induction HV; simpl; econstructor; eauto. }
    split; intro HV.
    - apply FWD. exact HV.
    - destruct (renaming_inv r) as [r' INV]. apply (FWD r') in HV.
      rewrite (re_rename_expr r' r INV) in HV. rewrite (re_rename_state r' r INV) in HV.
      exact HV.
  Qed.
    
End Renaming.
