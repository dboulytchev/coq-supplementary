Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

Require Import List.
Import ListNotations.

From hahn Require Import HahnBase.

Require Import Stdlib.Program.Equality.

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
  Proof. assert ((exists z, s / x => z) \/ (~(exists z, s / x => z))) by tauto.
  destruct H.
  - destruct H as [z]. replace Z.zero with (z * Z.zero)%Z.
    + auto.
    + apply Z.mul_0_r.
  - Abort.

  Lemma not_zero_always: exists (x: id) (s: state Z),
    ~([|Var x [*] Nat 0|] s => Z.zero).
  Proof. exists (Id 0). exists []. intros H. inversion H. subst. inversion VALA. subst.
  apply st_not_binds_empty in VAR. destruct VAR. Qed.

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. apply bs_Nat. Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. inversion HH. inversion VALB. replace (za * 2)%Z with (za + za)%Z.
  - apply bs_Add; apply VALA.
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
Proof. generalize dependent z. induction e.
- intros. inversion HSub. exists z. auto.
- intros. inversion HSub. exists z. auto.
- intros. inversion HSub.
  + eauto.
  + inversion HV; eauto.
  + inversion HV; eauto.
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
Proof. generalize dependent z. induction e; intros.
- exists z. inversion ID.
- exists z. inversion ID. inversion RED. subst id. apply VAR.
- inversion ID. destruct H3; inversion_clear RED; inversion H3; eauto.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. induction e; unfold not; intros.
- specialize UNDEF with z0. inversion ID.
- specialize UNDEF with z. inversion ID. inversion H. subst id. auto.
- specialize UNDEF with z. inversion ID. destruct H4; apply UNDEF; subst.
  + inversion H; exfalso; unfold not in IHe1; specialize IHe1 with za; apply IHe1; auto.
  + inversion H; exfalso; unfold not in IHe2; specialize IHe2 with zb; apply IHe2; auto.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. generalize dependent z1. generalize dependent z2. induction e; intros.
- inversion E1; inversion E2; subst; auto.
- inversion E1; inversion E2; subst; apply (state_deterministic Z s i _); auto.
- inversion E1; inversion E2; subst; specialize IHe1 with za0 za;
  specialize IHe2 with zb0 zb; apply IHe1 in VALA0; apply IHe2 in VALB0; congruence.
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof. generalize dependent z. induction e.
- intros. inversion EV. constructor.
- intros. inversion EV. constructor. specialize FV with i. apply FV; auto.
- intros. inversion EV; try constructor; try apply IHe1; try apply IHe2; intros;
  try apply FV; auto;
  econstructor; eauto.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. unfold equivalent. reflexivity. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. unfold equivalent. symmetry. apply EQ. Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. unfold equivalent. intros. transitivity ([|e2|] s => n); auto. Qed.

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
Proof. split.
- intros. unfold contextual_equivalent. induction C.
  + apply H.
  + split; intros; inversion H0; econstructor; eauto; apply IHC; auto.
  + unfold equivalent. intros.
    split; intros; inversion H0; econstructor; eauto; apply IHC; auto.
- intros. unfold contextual_equivalent in H. specialize H with Hole. auto.
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
  Proof. induction HE.
  - auto.
  - inversion HE.
    + subst. apply (reach_step s e (Nat z)).
      * apply HStep.
      * apply IHHE.
    + subst. apply (reach_step s e e').
      * apply HStep.
      * apply IHHE.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof. remember (Nat z) as ez. induction HR.
  - destruct e.
    + apply se_Stop.
    + discriminate.
    + discriminate.
  - apply (se_Step s e e' e'').
    + apply HStep.
    + apply IHHR. apply Heqez.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.

  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof. induction H1.
  - destruct e''; inversion H2. (* There is no constructor (ss_step Nat ...) -- contradiction *)
  - apply IHss_eval in H2. apply (se_Step s e e' e'').
    + apply HStep.
    + apply H2.
  Qed.

  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof. induction H1.
  - apply H2.
  - eauto.
  Qed.

  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof. inversion HV. unfold normal_form. unfold not. intros.
  inversion H0. inversion H1. (* again, no constructor from Nat *)
  Qed.

  (* Looks like this thing should be in standard library... *)
  Lemma not_impl: forall (P Q: Prop),
    P -> ~Q -> ~(P -> Q).
  Proof. auto. Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. apply ex_not_not_all. exists (Nat 1 [/] Nat 0). apply not_impl.
  - unfold normal_form. intros. apply all_not_not_ex. unfold not. intros. inversion_clear H.
    + inversion LEFT.
    + inversion RIGHT.
    + inversion_clear EVAL. inversion VALB. auto.
  - unfold not. intros. inversion H.
  Qed.

  Lemma not_impl': forall (P Q T: Prop),
    P -> Q -> ~T -> ~(P -> Q -> T).
  Proof. auto. Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    apply ex_not_not_all. exists ((Nat 1 [+] Nat 2) [+] (Nat 3 [+] Nat 4)).
    apply ex_not_not_all. exists (Nat 3 [+] (Nat 3 [+] Nat 4)).
    apply ex_not_not_all. exists ((Nat 1 [+] Nat 2) [+] Nat 7).
    apply ex_not_not_all. exists [].
    apply not_impl'.
    - apply ss_Left. apply ss_Bop. apply (bs_Add _ _ _ 1 2); constructor.
    - apply ss_Right. apply ss_Bop. apply (bs_Add _ _ _ 3 4); constructor.
    - congruence.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. induction Heval.
  - constructor.
  - apply IHHeval.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof. generalize dependent C. induction HR.
  - auto.
  - intros C. apply (reach_step _ (C <~ e) (C <~ e') (C <~ e'')).
    + induction C.
      * auto.
      * simpl. apply (ss_Left _ (C <~ e) e0 (C <~ e') _). apply IHC.
      * simpl. apply (ss_Right _ e0 (C <~ e) (C <~ e') _). apply IHC.
    + apply IHHR.
  Qed.

  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof. induction HR1.
  - induction HR2.
    + auto.
    + apply (reach_step _ (Bop op e e0) (Bop op e e') _).
      * auto.
      * apply IHHR2.
  - apply (reach_step _ (Bop op e e2) (Bop op e' e2) _).
    + auto.
    + apply IHHR1.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof. inversion H;
  (* Arithmetic *)
  subst; econstructor; eauto;
  assert (za = za0) by ( apply (eval_deterministic e1 s); auto ); subst;
  assert (zb = zb0) by ( apply (eval_deterministic e2 s); auto ); subst; auto;
  (* Relations *)
  constructor; eauto.
  Qed.

  #[export] Hint Resolve ss_bop_reachable : core.

  Lemma ss_eval_binop s e1 e2 za zb z op
        (IHe1 : (s) |- e1 -->> (Nat za))
        (IHe2 : (s) |- e2 -->> (Nat zb))
        (H    : [|Bop op e1 e2|] s => z)
        (VALA : [|e1|] s => (za))
        (VALB : [|e2|] s => (zb)) :
        s |- Bop op e1 e2 -->> (Nat z).
  Proof. assert (s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z)).
    { eauto. }
  apply ss_reachable_eval. apply (ss_reachable_trans s (Bop op e1 e2) (Bop op (Nat za) (Nat zb)) _).
  - apply ss_subst_binop; auto.
  - apply H0.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

  Lemma ss_eval_nat_nat: forall (s: state Z) (n1 n2: Z),
    (s |- (Nat n1) -->> (Nat n2)) -> n1 = n2.
  Proof. intros. inversion H.
  - reflexivity.
  - subst. inversion HStep.
  Qed.

  Lemma ss_step_bs_eval'' (e e1: expr) (s: state Z) (z: Z):
    s |- e --> e1 -> [|e1|] s => z -> [|e|] s => z.
  Proof. intros. generalize dependent e. dependent induction H0; intros;
  (dependent destruction H; econstructor) + inversion H; eauto.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. split; intros.
  - induction H; eauto.
  - generalize dependent z. induction e; intros.
    + apply (ss_eval_nat_nat s z z0) in H. subst. auto.
    + inversion H. inversion HStep. subst. apply (ss_eval_nat_nat s z0 z) in Heval. subst. auto.
    + clear IHe1. clear IHe2. remember (Nat z). induction H.
      * rewrite Heqe. apply bs_Nat.
      * subst. apply (ss_step_bs_eval'' e e').
        { apply HStep. }
        { apply IHss_eval. reflexivity. }
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
  Proof. destruct t2;
  inversion H1; inversion H2; constructor.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof. inversion H1.
  - reflexivity.
  - subst. inversion H2.
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
  (* The definition of typeOf is wrong (see Example bad_type), so this lemma cannot be proven.
  But even if typeOf was defined properly, this lemma states that, if we select *arbitary* type
  t' such that t' << t, the expression e' will have this type, which is definetly false.
  The correct statement is type_preservation' below *)

  Ltac is_zbool :=
  match goal with
  | |-  (zbool Z.one) => constructor 1; auto
  | |- (zbool 1) => constructor 1; auto
  | |- (zbool Z.zero) => constructor 2; auto
  | |- (zbool 0) => constructor 2; auto
  end.

  Example bad_type: ~((Nat 1 [+] Nat 1) :-: Bool) /\ ~((Nat 1 [+] Nat 1) :-: Int).
  split.
  - intros H. inversion H.
  - intros H. inversion H. inversion H0. destruct HNbool. is_zbool.
  Qed.

  Lemma typeof_det e t1 t2 (HT1: e :-: t1) (HT2: e :-: t2): t1 = t2.
  Proof. inversion HT1; inversion HT2; subst; auto;
  (* Some contradictory cases *)
  try congruence;
  (* Some strange contradictory cases *)
  inversion H1; destruct HNbool; subst; is_zbool.
  Qed.

  Lemma ss_step_preserves_type (e1 e2: expr) (st: state Z) (t1 t2: Typ)
        (HT: e1 :-: t1) (STEP: st |- e1 --> e2) (HT': e2 :-: t2):
    t2 << t1.
  Proof.
  generalize dependent t2. generalize dependent t1. dependent induction STEP; intros;
  inversion HT; subst; try inversion HT'; try constructor;
    (* Some strange contradictory cases that cannot be handled by the common pattern *)
    try (inversion EVAL; destruct HNbool; subst; is_zbool);
    (* And more special cases. Maybe there is a shorter way?.. *)
    inversion EVAL; destruct HNbool; destruct BOOLA; subst.
    + destruct BOOLB; subst.
      * constructor 1. auto.
      * constructor 2. auto.
    + constructor 2. subst. auto.
    + destruct BOOLB; subst; constructor 1; auto.
    + destruct BOOLB; subst.
      * constructor 1. auto.
      * constructor 2. auto.
  Qed.

  (* This lemma is false with the current deinition of typeOf. But it's the only place where
  is shoots -- if we admit here, all other things can be proven easily *)
  Lemma exists_type (e1 e2: expr) (st: state Z) (t: Typ)
      (STEP: st |- e1 --> e2) (T1: e1 :-: t):
    exists t2, e2 :-: t2.
  Proof. admit. Admitted.

  Lemma type_preservation' e t (HT: e :-: t):
    forall st e' t' (HR: st |- e ~~> e') (HT': e' :-: t'), t' << t.
  Proof. intros. destruct t.
  - destruct t'; constructor.
  - dependent induction HR.
    + assert (t' = Bool). { apply typeof_det with (e := e); auto. }
      subst. constructor.
    + apply IHHR.
      * apply exists_type with (t := Bool) in HStep as HT2; auto. destruct HT2 as [te'].
        apply ss_step_preserves_type with (t1 := Bool) (t2 := te') in HStep; auto.
        inversion HStep. subst. auto.
      * apply HT'.
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof. generalize dependent e. induction e.
  - intros. inversion HVal. subst. inversion HT; unfold zbool; auto.
  - intros. inversion HT.
  - intros. inversion HT;
    inversion HVal; subst; try congruence;
    (* 0 and 1 *)
    unfold zbool; auto;
    (* And and Or *)
    inversion BOOLA; inversion BOOLB; subst; auto.
  Qed.

End StaticSemantics.

Module Renaming.

  Definition renaming := { f : id -> id | Bijective f }.

  Definition rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.

  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof. destruct r as [f]. destruct b as [g]. destruct a.
  exists (exist _ g (ex_intro _ _ (conj e0 e))). auto.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. destruct r as [f]. destruct b as [g]. destruct a.
  assert (Bijective g).
    { unfold Bijective. exists f. auto. }
  exists (exist _ g H). auto.
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
  Proof. unfold renamings_inv in Hinv. induction e.
  - simpl. reflexivity.
  - simpl. f_equal. apply Hinv.
  - simpl. f_equal; auto.
  Qed.

  Fixpoint rename_state (r : renaming) (st : state Z) : state Z :=
    match st with
    | [] => []
    | (id, x) :: tl =>
        match r with exist _ f _ => (f id, x) :: rename_state r tl end
    end.

  Lemma rename_state_id (r: renaming) (i: id) (z: Z):
    rename_state r [(i, z)] = [(rename_id r i, z)].
  Proof. destruct r. simpl. reflexivity. Qed.

  Lemma cons_app (T: Type) (hd: T) (tl: list T):
    hd :: tl = [hd] ++ tl.
  Proof. reflexivity. Qed.

  Lemma rename_state_dist_unary (r: renaming) (i: id) (z: Z) (tl: state Z):
    rename_state r ((i, z) :: tl) = [(rename_id r i, z)] ++ (rename_state r tl).
  Proof. destruct r. simpl. reflexivity. Qed.

  Lemma rename_state_dist (r: renaming) (s1 s2: state Z):
    rename_state r (s1 ++ s2) = (rename_state r s1) ++ (rename_state r s2).
  Proof. induction s1.
  - simpl. reflexivity.
  - replace (a :: s1) with ([a] ++ s1) by auto.
    rewrite <- app_assoc.
    replace (rename_state r ([a] ++ (s1 ++ s2))) with ((rename_state r [a]) ++ (rename_state r (s1 ++ s2))).
    + replace (rename_state r ([a] ++ s1)) with ((rename_state r [a]) ++ rename_state r (s1)).
      * rewrite <- app_assoc. f_equal. apply IHs1.
      * destruct a. replace ([(i, z)] ++ s1) with ((i, z) :: s1) by auto.
        rewrite (rename_state_dist_unary r i z s1). rewrite rename_state_id. reflexivity.
    + remember (s1 ++ s2) as s. destruct a. replace ([(i, z)] ++ s) with ((i, z) :: s) by auto.
      rewrite (rename_state_dist_unary r i z s). rewrite rename_state_id. reflexivity.
  Qed.

  Lemma re_rename_state
    (r r' : renaming)
    (Hinv : renamings_inv r r')
    (st   : state Z) : rename_state r (rename_state r' st) = st.
  Proof. unfold renamings_inv in Hinv. induction st.
  - simpl. reflexivity.
  - replace (a :: st) with ([a] ++ st).
    + rewrite rename_state_dist. rewrite rename_state_dist.
      rewrite IHst. destruct a. rewrite rename_state_id. rewrite rename_state_id. rewrite Hinv. reflexivity.
    + auto.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. unfold Bijective in BH. destruct BH as [g [H1 H2]]. unfold Injective.
  intros. assert (g (f x) = g (f y)).
    { f_equal. apply H. }
  rewrite H1 in H0. rewrite H1 in H0. apply H0.
  Qed.

  (* Silly statement, but it's convenient to have it as a separate lemma *)
  Lemma nat_eval_any_state (n n': Z) (s1 s2: state Z):
    [|Nat n|] s1 => n' <-> [|Nat n|] s2 => n'.
  Proof. split.
  - intros. inversion H. subst. constructor.
  - intros. inversion H. subst. constructor.
  Qed.

  Lemma rename_id_inj (r: renaming) (i1 i2: id) (EQ: rename_id r i1 = rename_id r i2):
    i1 = i2.
  Proof. destruct r as [f b]. simpl in EQ. apply bijective_injective in b. apply b. apply EQ. Qed.

  Lemma rename_id_state_tail (r: renaming) (s: state Z) (i i0: id) (z z0: Z) (NEQ: i <> i0):
    (rename_state r ((i0, z0) :: s)) / (rename_id r i) => z <-> (rename_state r s) / (rename_id r i) => z.
  Proof. replace ((i0, z0) :: s) with ([(i0, z0)] ++ s) by auto.
  rewrite rename_state_dist. rewrite rename_state_id. simpl.
  split; intros H; inversion H; subst;
  try (apply rename_id_inj in H4; subst; congruence);
  try apply H6;
  constructor;
  ((intros NEQ2; apply rename_id_inj in NEQ2) + constructor);
  congruence.
  Qed.

  Lemma rename_id_state (r: renaming) (s: state Z) (i: id) (z: Z):
    s / i => z <-> (rename_state r s) / (rename_id r i) => z.
  Proof. induction s.
  - simpl. split; intros H; apply st_not_binds_empty in H; destruct H.
  - destruct a. destruct (id_eq_dec i i0).
    + subst. replace ((i0, z0) :: s) with ([(i0, z0)] ++ s) by auto.
      rewrite rename_state_dist. rewrite rename_state_id. simpl. split;
      intros H; inversion_clear H;
      try constructor;
      congruence.
    + split.
      * intros. rewrite rename_id_state_tail by congruence. rewrite <- IHs. inversion H; subst; congruence.
      * intros. rewrite rename_id_state_tail in H by congruence. constructor.
        { congruence. }
        { rewrite IHs. apply H. }
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. generalize dependent z. induction e.
  - intros. simpl. induction st.
    + reflexivity.
    + apply nat_eval_any_state.
  - intros. induction st.
    + simpl. split; intros; inversion H; subst; inversion VAR.
    + split;
      intros; constructor; replace (a :: st) with ([a] ++ st) by auto;
      replace (a :: st) with ([a] ++ st) in H by auto.
      * rewrite <- rename_id_state. inversion_clear H. apply VAR.
      * inversion_clear H. rewrite <- rename_id_state in VAR. apply VAR.
  - simpl. split;
    intros; inversion_clear H;
    econstructor; ((apply IHe1; apply VALA) + (apply IHe2; apply VALB) + congruence).
  Qed.

End Renaming.
