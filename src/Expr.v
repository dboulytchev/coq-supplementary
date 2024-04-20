Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

Require Import List.
Import ListNotations.

Require Import Coq.Program.Equality.

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
  Proof. constructor. Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    dependent destruction HH; dependent destruction HH1; dependent destruction HH2;
    rewrite <- Zplus_diag_eq_mult_2;
    try constructor; try constructor; try assumption.
    all: dependent destruction a; dependent destruction b; econstructor; eassumption.
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
    dependent induction HSub.
    * exists z. assumption.
    * dependent destruction HV.
      all: specialize (IHHSub s za HV1);
           dependent destruction IHHSub;
           econstructor; try econstructor; try eassumption.
    * dependent destruction HV.
      all: specialize (IHHSub s zb HV2);
           dependent destruction IHHSub;
           econstructor; try econstructor; try eassumption.
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
    induction RED; dependent destruction ID.
    exists z. assumption.
    all: dependent destruction H;
        [ apply IHRED1; assumption
        | apply IHRED2; assumption
        ].
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
    intros until 1.
    destruct (defined_expression e s z id); try assumption.
    contradiction (UNDEF x).
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z)
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
    dependent induction e; dependent destruction E1; dependent destruction E2.
    reflexivity. apply (state_deterministic Z s i); assumption.
    all: specialize (IHe1 s za za0 E1_1 E2_1); try rewrite IHe1; try rewrite IHe1 in OP;
         specialize (IHe2 s zb zb0 E1_2 E2_2); try rewrite IHe2; try rewrite IHe2 in OP;
         try reflexivity; try lia; try contradiction (OP0 OP); try contradiction (OP OP0).
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
    induction EV.
    constructor.
    constructor. apply FV. constructor. assumption.
    all: econstructor;
        try ( apply IHEV1; intros; apply FV; constructor; left; assumption );
        try ( apply IHEV2; intros; apply FV; constructor; right; assumption );
        assumption.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z),
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. intro. intro. constructor; intro; assumption. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. intro. intro. constructor; intro; apply EQ; assumption. Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3): e1 ~~ e3.
Proof.
    intro. intro. constructor.
    * intro. apply EQ2. apply EQ1. assumption.
    * intro. apply EQ1. apply EQ2. assumption.
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
    constructor.
    * intro. intro. induction C; constructor; intro; simpl; simpl in H0.

      apply H. assumption. apply H. assumption.
      all: dependent destruction b; dependent destruction H0;
           econstructor; try eapply IHC; eassumption; eassumption.

    * intro. intro. constructor; intro; simpl; simpl in H0; apply (H Hole); assumption.
Qed.

Module SmallStep.

  Inductive is_value : expr -> Prop :=
    isv_Intro : forall n, is_value (Nat n).

  Reserved Notation "st |- e --> e'" (at level 0).

  Inductive ss_step : state Z -> expr -> expr -> Prop :=
    ss_Var   : forall (s   : state Z)
                      (i   : id)
                      (z   : Z)
                      (VAL : s / i => z),
               (s |- (Var i) --> (Nat z))
  | ss_Left  : forall (s      : state Z)
                      (l r l' : expr)
                      (op     : bop)
                      (LEFT   : s |- l --> l'),
               (s |- (Bop op l r) --> (Bop op l' r))
  | ss_Right : forall (s      : state Z)
                      (l r r' : expr)
                      (op     : bop)
                      (RIGHT  : s |- r --> r'),
               (s |- (Bop op l r) --> (Bop op l r'))
  | ss_Bop   : forall (s       : state Z)
                      (zl zr z : Z)
                      (op      : bop)
                      (EVAL    : [| Bop op (Nat zl) (Nat zr) |] s => z),
               (s |- (Bop op (Nat zl) (Nat zr)) --> (Nat z))
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
    dependent destruction HV.
    intro. intro.
    dependent destruction H.
    dependent destruction H.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intro.
    assert (H1 : is_value (Nat 1 [/] Nat 0)).
    * eapply H. intro. intro. dependent destruction H0. dependent destruction H0.
      - dependent destruction H0.
      - dependent destruction H0.
      - dependent destruction EVAL. dependent destruction EVAL2. apply NZERO. reflexivity.
    * inversion H1.
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z),
    s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    intro.
    absurd ((Nat 1 [+] Var (Id 2)) = (Var (Id 1) [+] Nat 2)).
    * intro. inversion H0.
    * apply (H
        (Var (Id 1) [+] Var (Id 2))
        (Nat 1 [+] Var (Id 2))
        (Var (Id 1) [+] Nat 2)
        ((Id 2, Zpos 2) :: (Id 1, Zpos 1) :: nil)).
      - constructor. constructor. constructor.
        + intro. inversion H0.
        + constructor.
      - constructor. constructor. constructor.
  Qed.

  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    induction e; dependent destruction H1; dependent destruction H2.
    * f_equal. apply (state_deterministic _ s i). assumption. assumption.
    * inversion H2.
    * inversion H2.
    * f_equal. apply (eval_deterministic (Bop b (Nat zl) (Nat zr)) s). assumption. assumption.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. dependent induction Heval. constructor. eassumption. Qed.

  Lemma ss_eval_lift1 (e1 e1' e2 : expr)
                     (s : state Z)
                     (op : bop)
                     (z : Z)
                     (H1 : s |- e1 -->> e1')
                     (H2 : s |- Bop op e1' e2 -->> (Nat z))
                : s |- Bop op e1 e2 -->> (Nat z).
  Proof.
    dependent induction H1.
    * assumption.
    * econstructor.
      - eapply ss_Left. eassumption.
      - eapply IHss_eval. eassumption.
  Qed.

  Lemma ss_eval_lift2 (e1 e2 e2' : expr)
                     (s : state Z)
                     (op : bop)
                     (z : Z)
                     (H1 : s |- e2 -->> e2')
                     (H2 : s |- Bop op e1 e2' -->> (Nat z))
                : s |- Bop op e1 e2 -->> (Nat z).
  Proof.
    dependent induction H1.
    * assumption.
    * econstructor.
      - eapply ss_Right. eassumption.
      - eapply IHss_eval. eassumption.
  Qed.

  Lemma ss_eval_lift (e1 e1' e2 e2' : expr)
                     (s : state Z)
                     (op : bop)
                     (z : Z)
                     (H1 : s |- e1 -->> e1')
                     (H2 : s |- e2 -->> e2')
                     (H3 : s |- Bop op e1' e2' -->> (Nat z))
                : s |- Bop op e1 e2 -->> (Nat z).
  Proof. eapply ss_eval_lift1. eassumption. eapply ss_eval_lift2. eassumption. eassumption. Qed.

  Lemma ss_eval_lift' (e1 e2 : expr)
                     (s : state Z)
                     (op : bop)
                     (z z1 z2 : Z)
                     (H1 : s |- e1 -->> (Nat z1))
                     (H2 : s |- e2 -->> (Nat z2))
                     (H3 : [| Bop op (Nat z1) (Nat z2) |] s => z)
                : s |- Bop op e1 e2 -->> (Nat z).
  Proof.
    eapply ss_eval_lift; try by eassumption. econstructor.
    * eapply ss_Bop. eassumption.
    * econstructor.
  Qed.

  Lemma ss_eval_concat (e1 e2 e3 : expr)
                       (s : state Z)
                       (H1 : s |- e1 -->> e2)
                       (H2 : s |- e2 -->> e3)
                : s |- e1 -->> e3.
  Proof.
    dependent induction H1.
    * assumption.
    * econstructor.
      - eassumption.
      - eapply IHss_eval. assumption.
  Qed.

  Lemma ss_eval_left (e1 e2 : expr)
                     (s : state Z)
                     (z : Z)
                     (op : bop)
                     (H : s |- Bop op e1 e2 -->> (Nat z))
                : exists z1, s |- e1 -->> (Nat z1) /\ s |- Bop op (Nat z1) e2 -->> (Nat z).
  Proof.
    dependent induction H. dependent destruction HStep.
    * assert (Hl : exists z', s |- l' -->> (Nat z') /\ s |- Bop op (Nat z') e2 -->> (Nat z)).
      - eapply IHss_eval. reflexivity. reflexivity.
      - dependent destruction Hl. dependent destruction H0. exists x. econstructor.
        + econstructor; eassumption.
        + assumption.
    * specialize (IHss_eval e1 r' z op).
      assert (Hl : exists z1, s |- e1 -->> (Nat z1) /\ s |- Bop op (Nat z1) r' -->> (Nat z)).
      - eapply IHss_eval; reflexivity.
      - dependent destruction Hl. dependent destruction H0. exists x. constructor.
        + assumption.
        + econstructor; try eapply ss_Right; eassumption.
    * exists zl. econstructor.
      - econstructor.
      - econstructor; try eapply ss_Bop; eassumption.
  Qed.

  Lemma ss_eval_right (e1 e2 : expr)
                      (s : state Z)
                      (z : Z)
                      (op : bop)
                      (H : s |- Bop op e1 e2 -->> (Nat z))
                : exists z2, s |- e2 -->> (Nat z2) /\ s |- Bop op e1 (Nat z2) -->> (Nat z).
  Proof.
    dependent induction H. dependent destruction HStep.
    * specialize (IHss_eval l' e2 z op).
      assert (Hr : exists z2, s |- e2 -->> (Nat z2) /\ s |- Bop op l' (Nat z2) -->> (Nat z)).
      - eapply IHss_eval; reflexivity.
      - dependent destruction Hr. dependent destruction H0. exists x. constructor.
        + assumption.
        + econstructor; try eapply ss_Left; eassumption.
    * assert (Hr : exists z', s |- r' -->> (Nat z') /\ s |- Bop op e1 (Nat z') -->> (Nat z)).
      - eapply IHss_eval. reflexivity. reflexivity.
      - dependent destruction Hr. dependent destruction H0. exists x. constructor.
        + econstructor; try eapply ss_Bop; eassumption.
        + assumption.
    * exists zr. econstructor.
      - econstructor.
      - econstructor; try eapply ss_Bop; eassumption.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    constructor; intro.
    * dependent induction H.
      constructor.
      econstructor. constructor. eassumption. constructor.
      all: try by eapply ss_eval_lift'; (try by eassumption); econstructor; econstructor.
      all: eapply ss_eval_lift'; (try by eassumption); econstructor;
           (try by econstructor); eassumption.
    * dependent induction e.
      - dependent destruction H.
        + constructor.
        + dependent destruction H; inversion HStep.
      - dependent destruction H. dependent destruction HStep. dependent destruction H.
        + constructor. assumption.
        + inversion HStep.
      - specialize (ss_eval_left _ _ _ _ _ H). intro.
        dependent destruction H0. dependent destruction H0.
        specialize (ss_eval_right _ _ _ _ _ H1). intro.
        dependent destruction H2. dependent destruction H2.
        dependent destruction H3. dependent destruction HStep; try by inversion HStep.
        dependent destruction EVAL; dependent destruction EVAL1;
        dependent destruction EVAL2; dependent destruction H3.

        all: try by inversion HStep.
        all: try by econstructor; [ apply IHe1; eassumption | apply IHe2; eassumption | .. ].
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
  Proof. destruct r, b, a. exists (exist _ _ (ex_intro _ x (conj e0 e))). auto. Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. destruct r, b, a. exists (exist _ _ (ex_intro _ x (conj e0 e))). auto. Qed.

  Lemma renamings_symm r r' (Hinv : renamings_inv r r') : renamings_inv r' r.
  Proof. destruct r, b, a, r', b, a. unfold renamings_inv in *. simpl in *. congruence. Qed.

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
    dependent induction e; simpl.
    * reflexivity.
    * rewrite Hinv. reflexivity.
    * rewrite IHe1, IHe2. reflexivity.
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
    dependent induction st; simpl.
    * reflexivity.
    * destruct a, r, b, a, r', b, a. unfold renamings_inv in *. simpl in *.
      rewrite IHst; auto. congruence.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. inversion BH. inversion H. congruence. Qed.

  Lemma state_renaming_invariance (x : id) (st : state Z) (z : Z) (r : renaming)
    : st / x => z <-> (rename_state r st) / rename_id r x => z.
  Proof.
    constructor; intro; (try by inversion H); dependent destruction r; dependent induction H.
    * constructor.
    * constructor.
      - intro. apply H. eapply bijective_injective. eassumption. eassumption.
      - eapply IHst_binds.
    * dependent destruction st. inversion x. dependent destruction p.
      dependent destruction x. rewrite (bijective_injective _ b _ _ x). constructor.
    * dependent destruction st. inversion x. dependent destruction p.
      dependent destruction x. simpl in H, H0, IHst_binds. constructor.
      - intro. apply H. congruence.
      - eapply IHst_binds; reflexivity.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r : renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    constructor; intro.
    * dependent induction H.
      all: try by econstructor; [ apply IHeval1 | apply IHeval2 | .. ].
      - constructor.
      - constructor. apply state_renaming_invariance. assumption.
    * dependent induction H; dependent destruction e; dependent destruction x.
      all: try by econstructor; [ apply (IHeval1 _ _ r) | apply (IHeval2 _ _ r) | .. ]; eauto.
      - constructor.
      - constructor. eapply state_renaming_invariance. eassumption.
  Qed.

End Renaming.
