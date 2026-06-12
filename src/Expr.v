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

Ltac apply_eval za zb :=
  try match goal with
    | |- eval (_ [+] _) _ _ =>  apply bs_Add
    | |- eval (_ [-] _) _ _ =>  apply bs_Sub
    | |- eval (_ [*] _) _ _ =>  apply bs_Mul
    | |- eval (_ [/] _) _ _ =>  apply bs_Div
    | |- eval (_ [%] _) _ _ => apply bs_Mod
    | |- eval (_ [&] _) _ _ =>  apply bs_And
    | |- eval (_ [\/] _) _ _ => apply bs_Or
    | |- eval (_ [<=] _) _ (Z.one) => apply bs_Le_T with za zb
    | |- eval (_ [<=] _) _ (Z.zero) => apply bs_Le_F with za zb
    | |- eval (_ [<] _) _ (Z.one) => apply bs_Lt_T with za zb
    | |- eval (_ [<] _) _ (Z.zero) => apply bs_Lt_F with za zb
    | |- eval (_ [>=] _) _ (Z.one) => apply bs_Ge_T with za zb
    | |- eval (_ [>=] _) _ (Z.zero) => apply bs_Ge_F with za zb
    | |- eval (_ [>] _) _ (Z.one) => apply bs_Gt_T with za zb
    | |- eval (_ [>] _) _ (Z.zero) => apply bs_Gt_F with za zb
    | |- eval (_ [==] _) _ (Z.one) => apply bs_Eq_T with za zb
    | |- eval (_ [==] _) _ (Z.zero) => apply bs_Eq_F with za zb
    | |- eval (_ [/=] _) _ (Z.one) => apply bs_Ne_T with za zb
    | |- eval (_ [/=] _) _ (Z.zero) => apply bs_Ne_F with za zb
  end.

#[export] Hint Constructors eval : core.

Module SmokeTest.

  Lemma zero_always x (s : state Z) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof. Abort.
  
  Lemma zero_always_f : ~ (forall x s, [| Var x [*] Nat 0 |] s => Z.zero).
  Proof.
   unfold not; intros H.
   specialize (H (Id 0) []).
   inversion H; subst.
   inversion VALA; subst.
   inversion VAR.
  Qed.
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. eauto.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH; subst. 
    inversion VALB; subst.
    replace (za * 2)%Z with (za + za)%Z.
    - apply bs_Add.
      + exact VALA.
      + exact VALA.
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

Lemma eval_Bop_left :
  forall op a b st z,
    [| Bop op a b |] st => z ->
    exists za, [| a |] st => za.
Proof.
  intros op a b st z H.
  inversion H; subst; eauto.
Qed.

Lemma eval_Bop_right :
  forall op a b st z,
    [| Bop op a b |] st => z ->
    exists zb, [| b |] st => zb.
Proof.
  intros op a b st z H.
  inversion H; subst; eauto.
Qed.

Lemma strictness (e e' : expr) (HSub : e' << e) (st : state Z) (z : Z) (HV : [| e |] st => z) :
  exists z' : Z, [| e' |] st => z'.
Proof.
  revert st z HV.
  induction HSub; intros st z HV.
  - exists z; assumption.
  - destruct (eval_Bop_left _ _ _ _ _ HV) as [za Ha].
    eapply IHHSub in Ha.
    exact Ha.
  - destruct (eval_Bop_right _ _ _ _ _ HV) as [zb Hb].
    eapply IHHSub in Hb.
    exact Hb.
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
  - inversion_clear RED.
    inversion ID; subst.
    exists z; assumption.
  - inversion RED; subst; inversion ID; subst; inversion H3; eauto.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z H.
  destruct (defined_expression e s z id H ID) as [z' Hs].
  specialize (UNDEF z').
  contradiction.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z2.
  induction E1; intros z2 E2; inversion E2; subst;
    try (apply (state_deterministic Z s i z z2); assumption);
    try reflexivity;
    try (apply IHE1_1 in VALA);
    try (apply IHE1_2 in VALB);
    try subst;
    try congruence.
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
  generalize dependent z.
  induction e; intros.
  - inversion EV; subst.
    constructor.
  - inversion EV. 
    subst.
    apply bs_Var. 
    apply (FV i (v_Var i)). 
    assumption.
  - inversion EV; subst;
    try (apply IHe1 in VALA; apply IHe2 in VALB; eauto; intuition).
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  unfold equivalent.
  intros n s.
  split; intro H; assumption.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent in *.
  intros n s.
  specialize (EQ n s).
  destruct EQ as [H12 H21].
  split; intro H; [apply H21 | apply H12]; assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in *.
  intros n s.
  specialize (EQ1 n s).
  specialize (EQ2 n s).
  destruct EQ1 as [H12 H21].
  destruct EQ2 as [H23 H32].
  split; intro H.
  - apply H23. apply H12. assumption.
  - apply H21. apply H32. assumption.
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
  - intros EQ C.
    induction C; simpl.
    + exact EQ.
    + split; intros H; inversion H; subst; econstructor; eauto; apply IHC; eauto.
    + split; intros H; inversion H; subst; econstructor; eauto; apply IHC; eauto.
  - intros CEQ.
    apply (CEQ Hole).
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
    - eapply reach_step.
      + exact HStep.
      + apply IHHE.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
  remember (Nat z) as ez.
  induction HR.
  - subst.
    apply se_Stop.
  - subst.
    eapply se_Step; eauto.
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
    - eapply se_Step.
      + exact HStep.
      + apply IHss_eval.
        exact H2.
  Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1.
    - exact H2.
    - eapply reach_step.
      + exact HStep.
      + apply IHss_reachable.
        exact H2.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    unfold normal_form.
    intros s Hcontra.
    destruct Hcontra as [e' Hstep].
    inversion HV; subst.
    inversion Hstep.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
  intro H.
  specialize (H (Nat 5 [%] Nat 0)).
  assert (normal_form (Nat 5 [%] Nat 0)).
  { unfold normal_form. intros s [e' Hstep].
    inversion Hstep; subst.
    - inversion LEFT.
    - inversion RIGHT.
    - inversion EVAL; subst.
      inversion VALB.
      auto.
  }
  apply H in H0.
  inversion H0.
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    unfold not. intros H.
    set (e   := (Nat 1 [+] Nat 1) [*] (Nat 1 [+] Nat 1)).
    set (e'  := Nat (1+1) [*] (Nat 1 [+] Nat 1)).
    set (e'' := (Nat 1 [+] Nat 1) [*] Nat (1+1)).
    assert (Hneq : e' <> e'').
    { unfold e', e''. intro Heq. inversion Heq. }
    assert (Hstep1 : [] |- e --> e').
    { unfold e, e'. apply ss_Left. apply ss_Bop. apply bs_Add; apply bs_Nat. }
    assert (Hstep2 : [] |- e --> e'').
    { unfold e, e''. apply ss_Right. apply ss_Bop. apply bs_Add; apply bs_Nat. }
    apply Hneq.
    exact (H e e' e'' [] Hstep1 Hstep2).
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; clear H1; subst.
    - inversion H2; subst.
      + pose proof (state_deterministic Z s i z z0 VAL VAL0). 
        congruence.
    - inversion H2; subst.
      + inversion LEFT.
      + inversion RIGHT.
      + pose proof (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z0 EVAL EVAL0).
        congruence.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval; [ apply isv_Intro | assumption ].
  Qed.

  Lemma step (s : state Z) (C : Context) (e e' : expr)
      (HStep : s |- e --> e') : s |- (C <~ e) --> (C <~ e').
  Proof.
    induction C; simpl.
    - assumption.
    - constructor; exact IHC.
    - constructor; exact IHC.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    generalize dependent C.
    induction HR; intros C.
    - apply reach_base.
    - pose proof (step s C e e' HStep) as HCStep.
      eapply reach_step.
      + exact HCStep.
      + apply IHHR.
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    eapply ss_reachable_trans with (e' := Bop op e1' e2).
    - change (Bop op e1 e2) with (BopL op Hole e2 <~ e1).
      change (Bop op e1' e2) with (BopL op Hole e2 <~ e1').
      apply ss_subst. exact HR1.
    - change (Bop op e1' e2) with (BopR op e1' Hole <~ e2).
      change (Bop op e1' e2') with (BopR op e1' Hole <~ e2').
      apply ss_subst. exact HR2.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    eapply reach_step; [apply ss_Bop | apply reach_base].
    inversion H; subst;
    try (
      assert (HeqA := eval_deterministic e1 s za _ VALA VALA0);
      assert (HeqB := eval_deterministic e2 s zb _ VALB VALB0);
      subst
    ); 
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
    eapply ss_reachable_trans with (e' := Bop op (Nat za) e2).
    { apply ss_eval_reachable in IHe1.
      change (Bop op e1 e2) with (BopL op Hole e2 <~ e1).
      change (Bop op (Nat za) e2) with (BopL op Hole e2 <~ Nat za).
      apply ss_subst. exact IHe1. }
    eapply ss_reachable_trans with (e' := Bop op (Nat za) (Nat zb)).
    { apply ss_eval_reachable in IHe2.
      change (Bop op (Nat za) e2) with (BopR op (Nat za) Hole <~ e2).
      change (Bop op (Nat za) (Nat zb)) with (BopR op (Nat za) Hole <~ Nat zb).
      apply ss_subst. exact IHe2. }
    eauto.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.
  
  Require Import Program.Equality.

  Lemma ss_eval_equiv_aux (s   : state Z)
                              (e e': expr)
                              (z : Z)
                              (HST: (s) |- e --> e')
                              (HEX: [|e'|] s => z) : [|e|] s => (z).
  Proof.
    dependent induction e;
    inversion HST; subst;
    inversion HEX; subst;
    eauto.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                        (s : state Z)
                        (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    constructor; intro.
    - dependent induction H; eauto.
    - dependent induction H; eauto.
      assert (H_eq: Nat z = Nat z) by reflexivity.
      apply IHss_eval in H_eq.
      eapply ss_eval_equiv_aux; [eexact HStep | eexact H_eq].
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
    induction H1.
    - exact H2.
    - inversion H2; subst.
      + constructor.
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

  Lemma type_preservation e t t' (HS: t' << t) (HT: e :-: t) : forall st e' (HR: st |- e ~~> e'), e' :-: t'.
  Proof. Abort.

  Lemma not_type_preservation_alt2 : 
  ~ (forall e t t' st e', t' << t -> e :-: t -> st |- e ~~> e' -> e' :-: t').
  Proof.
    intros H_false_pres.
    assert (HS : Bool << Int) by apply subt_base.
    assert (HR : [] |- (Var (Id 0)) ~~> (Var (Id 0))) by apply reach_base.
    assert (HT : (Var (Id 0)) :-: Int) by apply type_X.
    apply H_false_pres with (e := Var (Id 0)) (st := []) (e' := Var (Id 0)) in HS; 
      try assumption.
    inversion HS.
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    intros st z0 HVal.
    inversion HT; inversion HVal; subst.
    all: unfold zbool; try eauto;
        try (inversion BOOLA; inversion BOOLB; subst; eauto);
        try (inversion H0; subst; eauto).
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
    destruct Hbij as [g [Hleft Hright]].
    assert (Hbij_g : Bijective g).
    { exists f. split; assumption. }
    exists (exist _ g Hbij_g).
    unfold renamings_inv.
    intros x.
    simpl.
    apply Hleft.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [f Hbij].
    destruct Hbij as [g [Hleft Hright]].
    assert (Hbij_g : Bijective g).
    { exists f. split; assumption. }
    exists (exist _ g Hbij_g).
    unfold renamings_inv; simpl.
    apply Hright.
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
    unfold renamings_inv in Hinv.
    induction e; simpl; congruence || (rewrite IHe1; rewrite IHe2; reflexivity).
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
    destruct r as [f Hbij].
    destruct r' as [f' Hbij'].
    induction st.
    - simpl.
      reflexivity.
    - destruct a as [x v].
      simpl.
      unfold renamings_inv in Hinv.
      simpl in Hinv.
      rewrite Hinv.
      rewrite IHst.
      reflexivity.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    unfold Injective.
    intros x y Heq.
    destruct BH as [g [Hleft Hright]].
    rewrite <- Hleft with (x := x).
    rewrite Heq.
    rewrite Hleft.
    reflexivity.
  Qed.
  
  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. 
    assert (H_forward: forall e st z r, [| e |] st => z -> [| rename_expr r e |] (rename_state r st) => z).
    { intros. induction H.
      { apply bs_Nat. }
      { apply bs_Var. induction VAR; destruct r0; unfold rename_id.
        - simpl. apply st_binds_hd.
        - apply st_binds_tl; [
            assert (H5: Injective x0) by (apply bijective_injective; intuition);
            intros H6; apply H5 in H6; contradiction
          | try solve [ apply IHs; assumption | apply IHVAR ] 
          ].
      }
      all: simpl; 
          apply_eval za zb; 
          try solve [apply IHeval1 | apply IHeval2 | intuition]. 
    }
    split.
    - intros H_eval. apply H_forward. exact H_eval.
    - intros H_eval. specialize renaming_inv with r as [r' H'].
      replace st with (rename_state r' (rename_state r st)). 
      replace e with (rename_expr r' (rename_expr r e)).
      + apply H_forward. exact H_eval.
      + apply re_rename_expr; auto.
      + apply re_rename_state; auto.
  Qed.
End Renaming.
