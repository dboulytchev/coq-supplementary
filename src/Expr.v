Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

Require Import List.
Require Import Coq.Program.Equality.
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

Ltac apply_eval za zb :=
  try match goal with
    | |- eval (_ [+] _) _ _ =>  apply bs_Add
    | |- eval (_ [-] _) _ _ =>  apply bs_Sub
    | |- eval (_ [*] _) _ _ =>  apply bs_Mul
    | |- eval (_ [/] _) _ _ =>  apply bs_Div
    | |- eval (_ [%] _) _ _ =>  apply bs_Mod
    | |- eval (_ [<=] _) _ (Z.one)  => apply bs_Le_T with za zb
    | |- eval (_ [<=] _) _ (Z.zero) => apply bs_Le_F with za zb
    | |- eval (_ [<] _) _ (Z.one)  =>  apply bs_Lt_T with za zb
    | |- eval (_ [<] _) _ (Z.zero) =>  apply bs_Lt_F with za zb
    | |- eval (_ [>=] _) _ (Z.one)  =>  apply bs_Ge_T with za zb
    | |- eval (_ [>=] _) _ (Z.zero) =>  apply bs_Ge_F with za zb
    | |- eval (_ [>] _) _ (Z.one)  =>  apply bs_Gt_T with za zb
    | |- eval (_ [>] _) _ (Z.zero) =>  apply bs_Gt_F with za zb
    | |- eval (_ [==] _) _ (Z.one)  =>  apply bs_Eq_T with za zb
    | |- eval (_ [==] _) _ (Z.zero) =>  apply bs_Eq_F with za zb
    | |- eval (_ [/=] _) _ (Z.one)  =>  apply bs_Ne_T with za zb
    | |- eval (_ [/=] _) _ (Z.zero) =>  apply bs_Ne_F with za zb
    | |- eval (_ [&] _) _ _ =>  apply bs_And
    | |- eval (_ [\/] _) _ _ => apply bs_Or
  end.

Module SmokeTest.

  Lemma zero_always x (s : state Z) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof. Abort.

  Lemma zero_always_contra : ~ (forall x s, [| Var x [*] Nat 0 |] s => Z.zero).
  Proof.
    unfold not. intros zero_always.
    specialize zero_always with (Id 0) [].
    inversion zero_always. 
    inversion VALA. apply st_eval_binds in VAR. unfold st_eval in VAR. discriminate.
  Qed.
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. apply bs_Nat. Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. 
    inversion HH.
    inversion VALB.
    replace (za*2)%Z with (za+za)%Z.
    apply bs_Add.
    - assumption.
    - assumption.
    - apply Zplus_diag_eq_mult_2.
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
  generalize dependent e'.
  induction HV; intros; inversion HSub; 
  try solve [ apply IHHV1; assumption | apply IHHV2; assumption ].
  - exists n. apply bs_Nat.
  - exists z. apply bs_Var. assumption.
  - exists (za+zb)%Z. apply bs_Add; assumption.
  - exists (za-zb)%Z. apply bs_Sub; assumption.
  - exists (za*zb)%Z. apply bs_Mul; assumption.
  - exists (Z.div za zb). apply bs_Div; assumption.
  - exists (Z.modulo za zb). apply bs_Mod; assumption.
  - exists Z.one. apply bs_Le_T with za zb; assumption.
  - exists Z.zero. apply bs_Le_F with za zb; assumption.
  - exists Z.one. apply bs_Lt_T with za zb; assumption.
  - exists Z.zero. apply bs_Lt_F with za zb; assumption.
  - exists Z.one. apply bs_Ge_T with za zb; assumption.
  - exists Z.zero. apply bs_Ge_F with za zb; assumption.
  - exists Z.one. apply bs_Gt_T with za zb; assumption.
  - exists Z.zero. apply bs_Gt_F with za zb; assumption.
  - exists Z.one. apply bs_Eq_T with za zb; assumption.
  - exists Z.zero. apply bs_Eq_F with za zb; assumption.
  - exists Z.one. apply bs_Ne_T with za zb; assumption.
  - exists Z.zero. apply bs_Ne_F with za zb; assumption.
  - exists (za*zb)%Z. apply bs_And; assumption.
  - exists (zor za zb). apply bs_Or; assumption.
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
  induction e; intros; inversion ID; inversion RED.
  { exists z. rewrite <- H1. assumption. }
  all: destruct H3; try solve 
  [ apply IHe1 with (z := za); assumption 
  | apply IHe2 with (z := zb); assumption ].
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. 
  induction e; unfold not in *; intros a H; inversion ID; inversion H.
  { specialize UNDEF with a. rewrite H0 in *. apply UNDEF in VAR. contradiction. }
  all: destruct H4; 
  try solve
  [ apply IHe1 with za; assumption
  | apply IHe2 with zb; assumption ].
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. 
  generalize dependent z2.
  induction E1; intros; inversion E2.
  { reflexivity. }
  { apply state_deterministic with s i; assumption. }
  all: apply IHE1_1 in VALA; apply IHE1_2 in VALB; 
 try rewrite VALA, VALB; try reflexivity;
  rewrite VALA, VALB in OP.
  - unfold Z.le in OP. rewrite <- OP0 in OP. contradiction.
  - unfold Z.le in OP0. rewrite <- OP in OP0. contradiction.
  - unfold Z.ge in OP0. rewrite <- OP in OP0. contradiction.
  - unfold Z.ge in OP. rewrite <- OP0 in OP. contradiction.
  - unfold Z.ge in OP. rewrite <- OP0 in OP. contradiction.
  - unfold Z.ge in OP0. rewrite <- OP in OP0. contradiction.
  - unfold Z.le in OP0. rewrite <- OP in OP0. contradiction.
  - unfold Z.le in OP. rewrite <- OP0 in OP. contradiction.
  - apply OP0 in OP. contradiction.
  - apply OP in OP0. contradiction.
  - apply OP in OP0. contradiction.
  - apply OP0 in OP. contradiction.
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
  generalize dependent s1.
  generalize dependent s2.
  generalize dependent z.
  induction e; intros; inversion EV.
  { apply bs_Nat. }
  { apply bs_Var. apply FV. apply v_Var. assumption. }
  all: apply_eval za zb;
  try solve 
  [ apply IHe1 with s1; intros; try apply FV; try apply v_Bop; try left; assumption; assumption
  | apply IHe2 with s2; intros; try apply FV; try apply v_Bop; try right; assumption; assumption
  | apply IHe1 with s2; intros; try apply FV; try apply v_Bop; try left; assumption; assumption
  | apply IHe2 with s1; intros; try apply FV; try apply v_Bop; try right; assumption; assumption
  | assumption
  ].
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. unfold equivalent. intros. apply iff_refl. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. unfold equivalent. intros. apply iff_sym. apply EQ. Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. unfold equivalent. intros. apply iff_trans with ([|e2|] s => n). apply EQ1. apply EQ2. Qed.

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
  - unfold "_ ~c~ _". intros. induction C.
    { assumption. }
    all: unfold "_ ~~ _"; simpl; 
      destruct b; intros; split; intros H1; inversion H1; apply_eval za zb; try apply IHC; assumption.
  - intros H. unfold "_ ~c~ _" in H. specialize H with (BopR Add (Nat 0) Hole). simpl in H. 
    unfold "~~" in *. intros n s. split; intros H1.
    2: assert [|Nat 0 [+] e2|] s => (0+n).
    1: assert [|Nat 0 [+] e1|] s => (0+n).
    all: replace n with (0+n)%Z in *;
    try solve
    [ reflexivity
    | apply bs_Add; try apply bs_Nat; assumption
    | apply H in H0; inversion H0; inversion VALA; 
      replace za with 0%Z in *; replace zb with n in *; assumption
    ].
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
    - apply reach_step with e'; assumption.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z) as ez.
    induction HR.
    - destruct e; try discriminate.
      apply se_Stop.
    - apply se_Step with e'.
      * assumption.
      * apply IHHR. assumption.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.
  
  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof. 
    induction H1.
    - destruct e''; inversion H2.
    - apply se_Step with e'.
      * assumption.
      * apply IHss_eval. assumption.
  Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof. 
    induction H1.
    - assumption.
    - apply reach_step with e'.
      * assumption.
      * apply IHss_reachable. assumption.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof. inversion HV. unfold normal_form, not. intros s [x H1]. inversion H1. Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. 
    unfold not. intros H. specialize H with (Bop And (Nat 2) (Nat 2)).
    assert (H1: (is_value (Nat 2 [&] Nat 2)) -> False). { intros H1. inversion H1. }
    apply H1. apply H. unfold normal_form. intros. unfold not. intros [e H2]. inversion H2. 
    - inversion LEFT.
    - inversion RIGHT.
    - inversion EVAL. inversion VALA. 
      rewrite <- H13 in BOOLA. unfold zbool in BOOLA. destruct BOOLA; discriminate.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. 
    unfold not. intros H. specialize H with (Var (Id 0) [+] Var (Id 0)) 
                                            (Nat 0 [+] Var (Id 0)) 
                                            (Var (Id 0) [+] Nat 0) 
                                            [(Id 0, Z.zero)].
    assert (S1: ss_step [(Id 0, Z.zero)] (Var (Id 0) [+] Var (Id 0)) (Nat 0 [+] Var (Id 0))).
    { apply ss_Left. apply ss_Var. apply st_binds_hd. }
    apply H in S1.
    - inversion S1.
    - apply ss_Right. apply ss_Var. apply st_binds_hd. 
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; inversion H2; try congruence.
    - f_equal. apply state_deterministic with s i; congruence.
    - inversion LEFT; congruence.
    - inversion RIGHT; congruence.
    - rewrite <- H5 in H0. injection H0 as E1 E2 E3. rewrite <- E1, E2, E3 in *.
      destruct op; f_equal;
      match type of EVAL with | ([|?e|] ?s => _) => apply eval_deterministic with e s end; 
      assumption.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. 
    induction Heval.
    - apply isv_Intro.
    - apply IHHeval.
  Qed.

  Lemma context_step (s: state Z) (C: Context) (e e': expr) (HStep: ss_step s e e') : 
    ss_step s (C <~ e) (C <~ e').
  Proof.
    induction C.
    - apply HStep.
    - simpl. apply ss_Left. apply IHC.
    - simpl. apply ss_Right. apply IHC.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof. 
    induction HR.
    - apply reach_base.
    - apply reach_step with (C <~ e').
      * apply context_step. assumption.
      * apply IHHR.
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof. 
    generalize dependent e2.
    generalize dependent e2'.
    induction HR1; intros.
    - generalize dependent e. 
      induction HR2; intros.
      * apply reach_base.
      * apply reach_step with (Bop op e0 e'). { apply ss_Right. assumption. }
        apply IHHR2.
    - inversion HR2.
      * apply reach_step with (Bop op e' e2'). { apply ss_Left. assumption. }
        apply IHHR1. apply reach_base.
      * apply reach_step with (Bop op e e'0). { apply ss_Right. assumption. }
        apply reach_step with (Bop op e' e'0). { apply ss_Left. assumption. }
        apply IHHR1. assumption.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof. 
    apply reach_step with (Nat z).
    - apply ss_Bop. inversion H; apply_eval za zb; assert (za = za0); assert (zb = zb0);
      try solve 
      [ apply eval_deterministic with e2 s; assumption 
      | apply eval_deterministic with e1 s; assumption 
      | rewrite H5; apply bs_Nat
      | rewrite H6; apply bs_Nat
      | congruence
      ].
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
    - apply reach_step with (Nat z); try constructor.
      remember (Bop op e1 e2) as B.
      induction H; try (injection HeqB; injection HeqB); intros; subst; try discriminate;
      try (eapply eval_deterministic in VALA; try apply H);
      try (eapply eval_deterministic in VALB; try apply H0);
      subst; auto; 
      econstructor; eauto.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. 
    assert (HR: forall e s z, [| e |] s => z -> (s |- e -->> (Nat z))).
    { clear e. clear s. clear z. intros. generalize dependent z. induction e; intros z0 H.
      * inversion H. apply se_Stop.
      * inversion H. rewrite <- H2 in *. apply se_Step with (Nat z). apply ss_Var. assumption. apply se_Stop.
      * inversion H; apply ss_eval_binop with za zb;
        solve
        [ apply IHe1; assumption
        | apply IHe2; assumption 
        | congruence ]. }
    split. 
    - apply HR.
    - intros. dependent induction H.
      * constructor.
      * specialize IHss_eval with z. assert (H1: Nat z = Nat z). { reflexivity. }
        apply IHss_eval in H1. clear IHss_eval.
        generalize dependent z.
        dependent induction HStep; intros; subst.
        + inversion H1; subst. constructor. assumption.
        + inversion H1; apply IHHStep in VALA; 
          try solve [apply HR in VALA; assumption];
          apply_eval za zb; assumption.
        + inversion H1; apply IHHStep in VALB; 
          try solve [apply HR in VALB; assumption];
          apply_eval za zb; assumption.
        + inversion H1; subst. assumption.
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
  Proof. inversion H1; inversion H2; congruence. Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof. inversion H1; inversion H2; congruence. Qed.
  
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

  Lemma type_preservation_contra : not (forall e t t' st e', t' << t -> e :-: t -> st |- e ~~> e' -> e' :-: t').
  Proof.
    assert (HS: Bool << Int). { apply subt_base. }
    assert (HT: (Var (Id 0)) :-: Int). { apply type_X. } 
    unfold not. intros HTP.
    specialize HTP with (Var (Id 0)) Int Bool [] (Var (Id 0)).
    intros. apply HTP in HS.
    - inversion HS.
    - apply HT.
    - apply reach_base.
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof. 
    remember Bool as zb.
    induction HT; intros; try discriminate; inversion HVal; unfold zbool;
    try solve 
    [ right; reflexivity
    | left; reflexivity ].
    - inversion BOOLA; inversion BOOLB.
      { left. rewrite H, H4. reflexivity. }
      all: right; rewrite H, H4; reflexivity.
    - inversion BOOLA; inversion BOOLB; try solve [left; rewrite H, H4; reflexivity].
      * right. rewrite H, H4. reflexivity. 
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
    unfold renaming in r. unfold Bijective in r. destruct r as [r [g [e1 e2]]].
    assert (Bijective g). { unfold Bijective. exists r. split; assumption. }
    exists (exist Bijective g H).
    unfold renamings_inv. simpl. assumption.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [r [g [e1 e2]]].
    assert (Bijective g). { unfold Bijective. exists r. split; assumption. }
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
    - destruct r as [f Hf]. destruct r' as [g Hg]. destruct a as [i z].
      simpl. rewrite IHst. rewrite Hinv. reflexivity.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. 
    destruct BH as [g [e1 e2]].
    unfold Injective. intros x y H.
    assert (g (f x) = g (f y)). { rewrite H. reflexivity. }
    rewrite e1, e1 in H0. apply H0.
  Qed.
  
  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. 
    assert (H: forall e st z r, [| e |] st => z -> [| rename_expr r e |] (rename_state r st) => z).
    { intros. induction H.
      { apply bs_Nat. }
      { apply bs_Var. induction VAR; 
        destruct r0; unfold rename_id.
        - simpl. apply st_binds_hd.
        - apply st_binds_tl; try solve [apply IHs; assumption | apply IHVAR ].
          assert (H5: Injective x0). { apply bijective_injective. apply b. }
          unfold not. intros H6. apply H5 in H6. congruence. }
      all: simpl; apply_eval za zb; try solve [apply IHeval1 | apply IHeval2 | congruence]. }
    split; intros.
    - apply H. assumption.
    - specialize renaming_inv with r as [r' Hr].
      replace st with (rename_state r' (rename_state r st)). 
      replace e with (rename_expr r' (rename_expr r e)). 
      apply H. assumption.
      apply re_rename_expr; assumption.
      apply re_rename_state; assumption.
  Qed.
    
End Renaming.
