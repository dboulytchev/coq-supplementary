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

  Lemma zero_always x (s : state Z) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof. Abort.
  Lemma zero_always_is_false: ~(forall x (s : state Z), [| Var x [*] Nat 0 |] s => Z.zero).
  Proof.
    intro H.
    set (s := @nil (id * Z)).
    set (x := Id 0).
    specialize (H x s).
    inversion H. subst.
    inversion VALA. subst.
    unfold s in VAR.
    inversion VAR.
  Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH; subst.
    inversion VALB; subst.
    replace (za * 2)%Z with (za + za)%Z by lia.
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
  induction HSub; intros z HV.
  - exists z. assumption.
  - inversion HV; subst; eapply IHHSub; eauto.
  - inversion HV; subst; eapply IHHSub; eauto.
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
  revert z RED.
  induction e; intros zv RED; inversion ID; subst.
  - inversion RED; subst; eauto.
  - match goal with [ H : _ \/ _ |- _ ] => destruct H end;
    inversion RED; subst; eauto.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z Hev.
  destruct (defined_expression e s z id Hev ID) as [z' Hbind].
  apply (UNDEF z'). assumption.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  revert z2 E2.
  induction E1; intros z2 E2; inversion E2; subst; unfold Z.eq in *;
    try (eapply state_deterministic; eassumption);
    try (specialize (IHE1_1 _ VALA); specialize (IHE1_2 _ VALB); subst);
    solve [ reflexivity | lia | exfalso; lia
          | exfalso; apply OP;  assumption
          | exfalso; apply OP0; assumption ].
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
  revert z EV.
  induction e; intros zv EV.
  - inversion EV; subst. apply bs_Nat.
  - inversion EV; subst. apply bs_Var, FV; auto.
  - assert (FVa : forall id, id ? e1 -> equivalent_states s1 s2 id)
      by (intros; apply FV; apply v_Bop; left;  assumption).
    assert (FVb : forall id, id ? e2 -> equivalent_states s1 s2 id)
      by (intros; apply FV; apply v_Bop; right; assumption).
    inversion EV; subst; econstructor; eauto.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. unfold equivalent. intros. reflexivity. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. unfold equivalent in *. intros. symmetry. apply EQ. Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in *. intros n s. split; intro H.
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

Ltac inv_bop_re :=
  match goal with
  | [ H : [| Bop ?op _ _ |] _ => _ |- _ ] => inversion H; subst; clear H
  end.

Lemma plug_equiv_aux (C : Context) (e1 e2 : expr) (EQ : e1 ~~ e2) :
  (C <~ e1) ~~ (C <~ e2).
Proof.
  unfold equivalent in *.
  induction C; intros n s; simpl.
  - apply EQ.
  - split; intro H; inv_bop_re;
    solve [ econstructor; eauto; try (apply IHC; eassumption) ].
  - split; intro H; inv_bop_re;
    solve [ econstructor; eauto; try (apply IHC; eassumption) ].
Qed.

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  split; intro H.
  - unfold contextual_equivalent. intro C. apply plug_equiv_aux. assumption.
  - unfold contextual_equivalent in H. specialize (H Hole). simpl in H. assumption.
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
    - eapply reach_step; eauto.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z) as e'.
    induction HR.
    - subst. apply se_Stop.
    - subst. specialize (IHHR (@Logic.eq_refl _ (Nat z))). eapply se_Step; eauto.
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
    - apply IHss_eval in H2. eapply se_Step; eauto.
  Qed.

  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1.
    - assumption.
    - eapply reach_step; eauto.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    inversion HV; subst.
    unfold normal_form. intros s [e' H]. inversion H.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intro H.
    (* Nat 0 [/] Nat 0 is a normal form but not value (div by zero) *)
    pose (e := Nat 0 [/] Nat 0).
    assert (NF : normal_form e).
    { unfold normal_form. intros s [e' Hstep].
      inversion Hstep; subst.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL; subst.
        inversion VALA; subst. inversion VALB; subst.
        apply NZERO. reflexivity. }
    specialize (H e NF). inversion H.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    intro H.
    (* (Nat 1 [+] Nat 1) [+] (Nat 1 [+] Nat 1) has two distinct steps *)
    pose (e3 := (Nat 1 [+] Nat 1) [+] (Nat 1 [+] Nat 1)).
    assert (Hin : [|Nat 1 [+] Nat 1|] [] => 2%Z).
    { replace 2%Z with (1 + 1)%Z by lia. apply bs_Add; apply bs_Nat. }
    assert (L : [] |- e3 --> (Nat 2 [+] (Nat 1 [+] Nat 1))).
    { apply ss_Left. apply ss_Bop. assumption. }
    assert (R : [] |- e3 --> ((Nat 1 [+] Nat 1) [+] Nat 2)).
    { apply ss_Right. apply ss_Bop. assumption. }
    pose proof (H _ _ _ _ L R) as Hcontra. inversion Hcontra.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    generalize dependent e'.
    remember (Nat z) as nz.
    induction H1; intros e2 H2.
    - subst. inversion H2; subst.
      f_equal. eapply state_deterministic; eassumption.
    - discriminate.
    - discriminate.
    - subst. inversion H2; subst.
      + inversion LEFT.
      + inversion RIGHT.
      + f_equal. eapply eval_deterministic; eassumption.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - constructor.
    - assumption.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction C; simpl.
    - assumption.
    - induction IHC.
      + apply reach_base.
      + eapply reach_step; [ apply ss_Left; eassumption | assumption ].
    - induction IHC.
      + apply reach_base.
      + eapply reach_step; [ apply ss_Right; eassumption | assumption ].
  Qed.

  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    pose proof (ss_subst s (BopL op Hole e2) e1 e1' HR1) as Hsub1.
    pose proof (ss_subst s (BopR op e1' Hole) e2 e2' HR2) as Hsub2.
    simpl in Hsub1, Hsub2.
    eapply ss_reachable_trans; eassumption.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    eapply reach_step.
    2: { apply reach_base. }
    apply ss_Bop.
    inversion H; subst;
      try (pose proof (eval_deterministic _ _ _ _ VALA VALA0) as Hza; subst);
      try (pose proof (eval_deterministic _ _ _ _ VALB VALB0) as Hzb; subst);
      try (econstructor; eauto using bs_Nat).
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
    apply ss_eval_reachable in IHe1.
    apply ss_eval_reachable in IHe2.
    pose proof (ss_subst_binop s e1 e2 (Nat za) (Nat zb) op IHe1 IHe2) as Hsub.
    pose proof (ss_bop_reachable s e1 e2 op za zb z H VALA VALB) as Hreach.
    pose proof (ss_reachable_trans _ _ _ _ Hsub Hreach) as Hfinal.
    apply ss_reachable_eval. assumption.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

  Lemma ss_step_preserves_eval (e e' : expr) (s : state Z) (z : Z)
        (HStep : s |- e --> e')
        (HEv : [| e' |] s => z) : [| e |] s => z.
  Proof.
    revert z HEv.
    induction HStep; intros zv IH.
    - inversion IH; subst. apply bs_Var. assumption.
    - inversion IH; subst;
      solve [ econstructor; eauto; apply IHHStep; assumption ].
    - inversion IH; subst;
      solve [ econstructor; eauto; apply IHHStep; assumption ].
    - inversion IH; subst. assumption.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    split.
    - intro H. induction H;
        try (eapply ss_eval_binop; eauto; econstructor; eassumption; fail).
      + apply se_Stop.
      + eapply se_Step; [ apply ss_Var; eassumption | apply se_Stop ].
    - intro H. remember (Nat z) as nz.
      induction H; subst.
      + inversion Heqnz; subst. apply bs_Nat.
      + eapply ss_step_preserves_eval; eauto.
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
    inversion H1; subst; inversion H2; subst;
      try constructor; try assumption.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof.
    inversion H1; subst; inversion H2; subst; reflexivity.
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
  Proof. admit. Admitted.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    remember Bool as tb.
    induction HT; intros st zv HVal; subst; try discriminate;
      inversion HVal; subst;
      try solve [left; reflexivity | right; reflexivity];
      destruct BOOLA as [Ha | Ha], BOOLB as [Hb | Hb]; subst;
        unfold zbool; try unfold zor; simpl; auto.
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
    assert (Hbij' : Bijective g).
    { exists f. split; assumption. }
    exists (exist _ g Hbij').
    unfold renamings_inv. simpl. intro x. apply Hgf.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [f Hbij].
    destruct Hbij as [g [Hgf Hfg]].
    assert (Hbij' : Bijective g).
    { exists f. split; assumption. }
    exists (exist _ g Hbij').
    unfold renamings_inv. simpl. intro x. apply Hfg.
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
    - reflexivity.
    - rewrite Hinv. reflexivity.
    - rewrite IHe1, IHe2. reflexivity.
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
    - destruct r' as [f' Hbij']. destruct r as [f Hbij]. reflexivity.
    - destruct a as [x v]. destruct r as [f Hbij]. destruct r' as [f' Hbij'].
      simpl. rewrite IHst.
      unfold renamings_inv in Hinv. simpl in Hinv. rewrite Hinv.
      reflexivity.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    destruct BH as [g [Hgf Hfg]].
    unfold Injective. intros x y Heq.
    apply (f_equal g) in Heq. rewrite Hgf, Hgf in Heq. assumption.
  Qed.
  
  Lemma rename_state_binds_fwd (st : state Z) (r : renaming) (x : id) (z : Z) :
    st / x => z -> (rename_state r st) / (rename_id r x) => z.
  Proof.
    intros H. induction H.
    - destruct r as [f Hbij]. simpl. apply st_binds_hd.
    - destruct r as [f Hbij]. simpl in *.
      apply st_binds_tl; auto.
      intro Heq. apply H. apply (bijective_injective f Hbij). assumption.
  Qed.

  Lemma rename_state_binds_bwd (st : state Z) (r : renaming) (x : id) (z : Z) :
    (rename_state r st) / (rename_id r x) => z -> st / x => z.
  Proof.
    induction st; intros H.
    - destruct r as [f Hbij]. simpl in H. inversion H.
    - destruct a as [y v]. destruct r as [f Hbij].
      destruct (id_eq_dec x y) as [Heq | Hneq].
      + subst y. simpl in H. inversion H; subst.
        * apply st_binds_hd.
        * exfalso. match goal with HH : f _ <> f _ |- _ => apply HH; reflexivity end.
      + apply st_binds_tl; auto.
        apply IHst.
        simpl in H. inversion H.
        * exfalso. apply Hneq.
          symmetry.
          apply (bijective_injective f Hbij).
          match goal with HH : f _ = f _ |- _ => exact HH end.
        * subst. assumption.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    split.
    - intro H. induction H; simpl;
        econstructor; eauto using rename_state_binds_fwd.
    - revert z. induction e; intros zv H; simpl in H; inversion H; subst;
        econstructor; eauto using rename_state_binds_bwd.
  Qed.
    
End Renaming.
