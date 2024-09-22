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
  Proof. constructor. Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH. subst.
    inversion VALB. subst.
    assert ((za * 2)%Z = (za + za)%Z).
    {
      induction za.
      {
        constructor.
      }
      {
        simpl.
        lia.
      }
      {
        simpl.
        lia.
      }
    }
    rewrite H.
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
Proof. admit. Admitted.

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
  generalize dependent z.
  induction e;
  intros.
  {
    inversion ID.
  }
  {
    inversion ID.
    inversion RED.
    subst.
    eauto.
  }
  {
    inversion ID.
    subst.
    inversion H3.
    {
      inversion RED;
      subst;
      eapply IHe1;
      eassumption.
    }
    {
      inversion RED;
      subst;
      eapply IHe2;
      eassumption.
    }
  }
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z EVAL.
  generalize dependent z.
  induction e;
  intros.
  {
    inversion ID.
  }
  {
    inversion ID.
    inversion EVAL.
    subst.
    specialize (UNDEF z).
    contradiction.
  }
  {
    inversion ID.
    inversion H3.
    {
      inversion EVAL;
      subst;
      eapply IHe1;
      eassumption.
    }
    {
      inversion EVAL;
      subst;
      eapply IHe2;
      eassumption.
    }
  }
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z)
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z1.
  generalize dependent z2.
  induction e;
  intros.
  {
    inversion E1.
    inversion E2.
    subst.
    reflexivity.
  }
  {
    inversion E1.
    inversion E2.
    subst.
    remember (state_deterministic Z s i z1 z2 VAR VAR0).
    subst.
    reflexivity.
  }
  {
    inversion E1;
    inversion E2;
    specialize (IHe1 za VALA za0 VALA0);
    specialize (IHe2 zb VALB zb0 VALB0);
    subst;
    try inversion H5;
    try reflexivity;
    try lia;
    try contradiction.
  }
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
  induction e;
  intros.
  {
    inversion EV.
    constructor.
  }
  {
    inversion EV.
    subst.
    specialize (FV i).
    assert (i ? (Var i)).
    {
      constructor.
    }
    specialize (FV H z).
    inversion FV.
    constructor.
    auto.
  }
  {
    assert (forall id : id, (id) ? (e1) -> equivalent_states s1 s2 id).
    {
      intros.
      apply (FV id).
      constructor.
      left.
      assumption.
    }

    assert (forall id : id, (id) ? (e2) -> equivalent_states s1 s2 id).
    {
      intros.
      apply (FV id).
      constructor.
      right.
      assumption.
    }

    inversion EV;
    subst;
    specialize (IHe1 H za VALA);
    specialize (IHe2 H0 zb VALB);
    econstructor;
    eauto.
  }
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z),
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. constructor; intuition. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent in EQ.
  constructor; intros; specialize (EQ n s).
  - apply EQ. assumption.
  - apply EQ. assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in EQ1.
  unfold equivalent in EQ2.
  constructor;
  specialize (EQ1 n s);
  specialize (EQ2 n s);
  inversion EQ1;
  inversion EQ2;
  auto.
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
  split;
  intros.
  {
    unfold contextual_equivalent.
    intro C.
    unfold equivalent.
    induction C;
    intros n s.
    {
      auto.
    }
    {
      simpl.
      split;
      intro.
      {
        inversion H0;
        subst;
        specialize (IHC za s);
        inversion IHC;
        specialize (H1 VALA);
        econstructor;
        eauto.
      }
      {
        inversion H0;
        subst;
        specialize (IHC za s);
        inversion IHC;
        specialize (H2 VALA);
        econstructor;
        eauto.
      }
    }
    {
      simpl.
      split;
      intro.
      {
        inversion H0;
        subst;
        specialize (IHC zb s);
        inversion IHC;
        specialize (H1 VALB);
        econstructor;
        eauto.
      }
      {
        inversion H0;
        subst;
        specialize (IHC zb s);
        inversion IHC;
        specialize (H2 VALB);
        econstructor;
        eauto.
      }
    }
  }
  {
    unfold contextual_equivalent in H.
    specialize (H Hole).
    simpl in H.
    assumption.
  }
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
    unfold not.
    intros.
    inversion HV.
    subst.
    inversion H.
    inversion H0.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.     unfold not.
    intros.
    unfold normal_form in H.
    specialize H with ((Nat 1) [/] (Nat 0)).

    assert (HA: (is_value (Nat 1 [/] Nat 0)) <-> False).
      { split.
        { intros. inversion H0. }
        { intros. inversion H0. } }

    apply HA.
    apply H.
    clear HA H.

    unfold not.
    intros.
    destruct H.
    inversion H; subst.
    { inversion LEFT. }
    { inversion RIGHT. }
    { inversion EVAL. subst.
      inversion VALB. subst. apply NZERO. reflexivity. }
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    unfold not.
    intros.
    remember ((Nat 1 [+] Nat 1) [+] (Nat 1 [+] Nat 1)) as e.
    remember ((Nat 2) [+] (Nat 1 [+] Nat 1)) as e'.
    remember ((Nat 1 [+] Nat 1) [+] (Nat 2)) as e''.
    specialize (H e e' e'' ([])).
    assert (([]) |- e --> (e')).
    {
      subst.
      repeat constructor.
      assert (2%Z = (1 + 1)%Z). lia.
      rewrite ->H0.
      constructor;
      auto.
    }
    assert (([]) |- e --> (e'')).
    {
      subst.
      repeat constructor.
      assert (2%Z = (1 + 1)%Z). lia.
      rewrite ->H1.
      constructor;
      auto.
    }
    specialize (H H0 H1).
    subst.
    inversion Heqe''.
  Qed.

  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1;
    inversion H2;
    subst;
    inversion H5;
    subst.
    {
      specialize (state_deterministic Z s i z z1 VAL VAL0).
      intro.
      subst.
      reflexivity.
    }
    {
      inversion LEFT.
    }
    {
      inversion RIGHT.
    }
    {
      specialize (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z1 EVAL EVAL0).
      intro.
      subst.
      reflexivity.
    }
  Qed.

  Lemma ss_step_same_eval (st : state Z)
                          (e e' : expr)
                          (z : Z)
                          (Heval : [| e |] st => z)
                          (Hstep : st |- e --> e') :
    [| e' |] st => z.
  Proof.
    generalize dependent z.
    induction Hstep;
    intros;
    subst.
    {
      inversion Heval.
      subst.
      specialize (state_deterministic Z s i z0 z VAR VAL).
      intro.
      subst.
      constructor.
    }
    {
      inversion Heval;
      subst;
      specialize (IHHstep za VALA);
      econstructor;
      eassumption.
    }
    {
      inversion Heval;
      subst;
      specialize (IHHstep zb VALB);
      econstructor;
      eassumption.
    }
    {
      specialize (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z0 EVAL Heval) as Heq.
      subst.
      constructor.
    }
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval; subst.
    - constructor.
    - assumption.
  Qed.

    Lemma ss_eval_equiv_induction_step (b: bop)
                          (e1 e2: expr)
                          (s: state Z)
                          (za zb: Z)
                          (VALA: [|e1|] s => za)
                          (VALB: [|e2|] s => zb)
                          (IHe1: (s) |- e1 -->> (Nat za))
                          (IHe2: (s) |- e2 -->> (Nat zb))
                          (z: Z)
                          (H: [|Bop b e1 e2|] s => (z)) :
    (s) |- Bop b e1 e2 -->> (Nat z).
  Proof.
    induction IHe1;
    induction IHe2.
    {
      econstructor.
      subst.
      {
        constructor 4.
        eassumption.
      }
      {
        constructor.
      }
    }
    {
      subst.
      econstructor.
      {
        constructor 3.
        eassumption.
      }
      {
        specialize (ss_step_same_eval s e e' zb VALB HStep) as Hss_step_same_eval.
        apply IHIHe2.
        {
          assumption.
        }
        {
          assumption.
        }
        {
          apply (ss_step_same_eval s (Bop b (Nat z0) e) (Bop b (Nat z0) e') z H).
          constructor.
          assumption.
        }
      }
    }
    {
      econstructor.
      {
        constructor 2.
        eassumption.
      }
      {
        specialize (ss_step_same_eval s e e' za VALA HStep) as Hss_step_same_eval.
        apply IHIHe1.
        {
          assumption.
        }
        {
          assumption.
        }
        {
          constructor.
        }
        {
          apply (ss_step_same_eval s (Bop b e (Nat z0)) (Bop b e' (Nat z0)) z H).
          constructor.
          assumption.
        }
      }
    }
    {
      assert ((s) |- e0 -->> (e''0)).
      {
        econstructor.
        eassumption.
        assumption.
      }

      specialize (ss_step_same_eval s e e' za VALA HStep) as Hss_step_same_eval.

      assert ([|Bop b e' e0|] s => z).
      {
        apply (ss_step_same_eval s (Bop b e e0) (Bop b e' e0) z H).
        constructor.
        assumption.
      }

      specialize (ss_step_same_eval s e e' za VALA HStep) as He'_eval_eq_za0.
      specialize (IHIHe1 He'_eval_eq_za0 VALB H0 H1).
      econstructor.
      {
        constructor.
        eassumption.
      }
      {
        assumption.
      }
    }
  Qed.

  Lemma ss_eval_equiv_left (e : expr)
                           (s : state Z)
                           (z : Z)
                           (H : [| e |] s => z) : s |- e -->> (Nat z).
  Proof.
    generalize dependent z.
    induction e;
    intros.
    {
      inversion H.
      subst.
      constructor.
    }
    {
      inversion H.
      subst.
      econstructor.
      {
        constructor.
        eassumption.
      }
      {
        constructor.
      }
    }
    {
      inversion H;
      revert H1;
      revert H4;
      subst;
      intros;
      specialize (IHe1 za VALA) as He1_step;
      specialize (IHe2 zb VALB) as He2_step;
      specialize (ss_eval_equiv_induction_step b e1 e2 s za zb VALA VALB He1_step He2_step z H);
      subst;
      intros;
      assumption.
    }
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    split;
    intros.
    {
      apply (ss_eval_equiv_left e s z H).
    }
    {
      dependent induction H;
      intros.
      {
        constructor.
      }
      {
        specialize (IHss_eval z).
        assert (Nat z = Nat z). constructor.
        apply IHss_eval in H0.
        clear IHss_eval.

        generalize dependent z.
        dependent induction e;
        intros.
        {
          inversion HStep.
        }
        {
          inversion HStep.
          subst.
          inversion H0.
          subst.
          constructor.
          assumption.
        }
        {
          inversion HStep;
          subst.
          {
            inversion H0;
            subst;
            assert ((s) |- l' -->> (Nat za)) as Hl'_ss_za;
            try apply (ss_eval_equiv_left l' s za VALA);
            try specialize (IHe1 l' LEFT za Hl'_ss_za VALA);
            try econstructor;
            try eassumption.
          }
          {
            inversion H0;
            subst;
            try assert ((s) |- r' -->> (Nat zb)) as Hr'_ss_zb;
            try apply (ss_eval_equiv_left r' s zb VALB);
            try specialize (IHe2 r' RIGHT zb Hr'_ss_zb VALB);
            try econstructor;
            try eassumption.
          }
          {
            inversion H0.
            subst.
            assumption.
          }
        }
      }
    }
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
  Proof.
    unfold renamings_inv.
    destruct  r.
    inversion b.

    assert (HA: Bijective x0).
      { unfold Bijective.
        destruct H.

        exists x. auto. }

    unfold renaming.

    exists (exist Bijective x0 HA).
    intros. simpl. unfold rename_id.
    destruct H.
    auto.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r.
    inversion b.
    destruct H.

    assert (HA: Bijective x0).
      { unfold Bijective.
        exists x. auto. }

    exists (exist Bijective x0 HA).
    unfold renamings_inv. intro.
    simpl. auto.
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
    - simpl.
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
    induction st.
    - reflexivity.
    - simpl.
      destruct a. simpl.
      destruct r'. simpl.
      destruct r. simpl.

      rewrite IHst.
      clear IHst.
      rewrite Hinv.

      reflexivity.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    unfold Injective.
    unfold Bijective in BH.
    intros.
    destruct BH. destruct H0.

    eapply f_equal in H.
    repeat erewrite H0 in H.

    assumption.
  Qed.

  Lemma renaming_inv_inv r1 : exists r2, renamings_inv r1 r2 /\ renamings_inv r2 r1.
  Proof.
    unfold renamings_inv.
    destruct  r1.
    inversion b.

    assert (HA: Bijective x0).
      { unfold Bijective.
        exists x. split; destruct H; auto. }

    exists (exist Bijective x0 HA).

    split; (intros; simpl; destruct H; auto).
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    split.
    - generalize dependent z; induction e; intros.
      + simpl.
        inversion H. subst.
        constructor.
      + simpl. unfold rename_id.
        destruct r.
        inversion H. subst.
        induction VAR; subst.
        { simpl. constructor. constructor. }
        { simpl.
          assert (HA: x id <> x id').
            { unfold not.
            intros.
            eapply bijective_injective in b as b'.
            apply b' in H1.
            contradiction H0. }

          constructor.
          eapply st_binds_tl.
          - assumption.
          - assert (HA': [|Var id|] st => x0).
              { constructor. assumption. }

             clear H VAR H0 HA.
             apply IHVAR in HA'. clear IHVAR.

             inversion HA'. subst.
             assumption. }

        + simpl. inversion H; subst;
          try (now
          apply IHe1 in VALA;
          apply IHe2 in VALB;
          econstructor; eassumption).
    - generalize dependent z. induction e; intros.
      + inversion H. subst. constructor.
      + simpl in H. inversion H; subst.

        dependent induction VAR.
        constructor.

        { destruct (renaming_inv r).

          clear H.
          eapply f_equal in x.

          assert (HA: st = rename_state x0 (rename_state r st)). {
            symmetry.
            eapply re_rename_state.
            assumption.
          }

          rewrite <- HA in x.
          rewrite <- x.
          simpl.
          destruct x0.
          unfold rename_id.
          destruct r.
          simpl.
          rewrite H0.
          constructor. }
        { destruct (renaming_inv_inv r).

          assert (HA: st = rename_state x0 (rename_state r st)). {
            symmetry.
            eapply re_rename_state.
            destruct H1.
            assumption.
          }

          eapply f_equal in x.
          rewrite <- HA in x.

          rewrite <- x.
          simpl. destruct x0.

          constructor.
          apply st_binds_tl.
          { unfold not in *.
            intros.
            apply H0.
            rewrite H2. clear H2.
            unfold rename_id. destruct r.

            destruct H1.
            apply H1. }
          { assert (HA': [|Var i|] ((rename_state (exist (fun f : id -> id => Bijective f) x0 b) st0)) => (z) ->
              st_binds Z (rename_state (exist (fun f : id -> id => Bijective f) x0 b) st0) i z).

              { intros. inversion H2. subst. assumption. }
              apply HA'. clear HA'.

              eapply IHVAR with r.
              + simpl.
                rewrite re_rename_state.
                { constructor. assumption. }
                destruct H1. auto.
              + reflexivity.
              + rewrite re_rename_state.
                { reflexivity. }
                destruct H1. auto.
              + reflexivity.
              + reflexivity. } (* TODO how to write it with `all` ?*)
        }
      + simpl in H.
        inversion H; subst; try (now
        apply IHe1 in VALA;
        apply IHe2 in VALB;
        econstructor; eassumption).
  Qed.

End Renaming.
