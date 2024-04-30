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

#[export] Hint Constructors eval.

Module SmokeTest.

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. 
    auto.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. 
    inversion HH.
    rewrite <- H0. rewrite <- H0 in VALA.
    assert ((za + za)%Z = (za * 2)%Z). intuition. 
    inv VALB. remember (bs_Add s e e za za VALA VALA). clear Heqe0. rewrite -> H in e0.
    assumption.
  Qed.

End SmokeTest.

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
  induction e; intros; inversion HSub; subst; try eauto.
  - inversion HV; eauto.
  - inversion HV; eauto.
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
  generalize dependent z.
  induction e; intros; inversion ID; subst.
  - inversion RED. econstructor. eassumption.
  - inversion RED; inversion H3; eauto.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. 
  generalize dependent UNDEF.
  induction e; intros; inversion ID; subst.
  - intuition. inversion H. eauto.
  - inversion H3; intuition; inversion H0; eauto.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. 
  generalize dependent z1. generalize dependent z2.
  induction e; intros.
  - inversion E1; inversion E2; subst. reflexivity.
  - inversion E1; inversion E2; subst. 
    eapply state_deterministic; eassumption.
  - destruct b; inversion E1; subst; inversion E2; subst; auto; subst;
    try (rewrite IHe1 with (z2:=za0) (z1:=za); 
            try reflexivity; try assumption; 
            rewrite IHe2 with (z2:=zb0) (z1:=zb); 
            try reflexivity; try assumption);
    by (rewrite IHe1 with (z2:=za) (z1:=za0) in *;
        try reflexivity; try assumption;
        rewrite IHe2 with (z2:=zb) (z1:=zb0) in *;
        try reflexivity; try assumption).
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
  generalize dependent z. induction e; intros.
  - inversion EV; subst; auto.
  - assert (i ? (Var i)). { constructor. }
    remember (FV i H).
    assert (s2 / i => z). { inversion EV. remember (e z). inversion i1. auto. }
    auto.
  - destruct b; inversion EV; subst.
    all: do 2
    match goal with
    | H: [|?e|] ?s => (?z) |- _ => 
      try (eapply IHe1 in H); try (eapply IHe2 in H);
      [ |intros; apply FV; constructor; intuition]
    end; auto; eauto.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. 
  constructor. auto. auto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. 
  constructor; remember (EQ n s); destruct i; assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. 
  constructor; remember (EQ1 n s); remember (EQ2 n s); 
  destruct i; destruct i0; auto.
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
  constructor; constructor; intro;
  generalize dependent n. 
  - induction C; intro; remember (H n s); 
    destruct i; auto; simpl; destruct b; intro; 
    inversion H0; subst. 
    all: try by (simpl; subst; 
                remember (IHC za VALA); auto).
    all: try (remember (IHC za VALA); auto).
    all: try (remember (IHC zb VALB); auto).
    * remember (bs_Le_T s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Le_F s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Lt_T s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Lt_F s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Ge_T s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Ge_F s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Gt_T s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Gt_F s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Eq_T s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Eq_F s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Ne_T s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Ne_F s (C <~ e2) e za zb e4 VALB OP). assumption.
    * remember (bs_Le_T s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Le_F s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Lt_T s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Lt_F s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Ge_T s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Ge_F s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Gt_T s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Gt_F s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Eq_T s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Eq_F s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Ne_T s e (C <~ e2) za zb VALA e4 OP). assumption.
    * remember (bs_Ne_F s e (C <~ e2) za zb VALA e4 OP). assumption.
  - induction C; intro; intro; simpl; auto.
    { remember (H n s). destruct i. auto. }
    all: simpl in H0; destruct b; inversion H0; subst.
    all: try (remember (IHC za VALA); auto).
    all: try (remember (IHC zb VALB); auto).
    * remember (bs_Le_T s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Le_F s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Lt_T s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Lt_F s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Ge_T s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Ge_F s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Gt_T s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Gt_F s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Eq_T s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Eq_F s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Ne_T s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Ne_F s (C <~ e1) e za zb e0 VALB OP). assumption.
    * remember (bs_Le_T s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Le_F s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Lt_T s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Lt_F s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Ge_T s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Ge_F s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Gt_T s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Gt_F s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Eq_T s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Eq_F s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Ne_T s e (C <~ e1) za zb VALA e0 OP). assumption.
    * remember (bs_Ne_F s e (C <~ e1) za zb VALA e0 OP). assumption.
  - remember (H Hole). simpl in e. 
    intro. remember (e n s). destruct i. assumption.
  - remember (H Hole). simpl in e. 
    intro. remember (e n s). destruct i. assumption.
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

  #[export] Hint Constructors ss_step.

  Reserved Notation "st |- e -->> e'" (at level 0).

  Inductive ss_eval : state Z -> expr -> expr -> Prop :=
    se_Stop : forall (s : state Z)
                     (z : Z),  s |- (Nat z) -->> (Nat z)
  | se_Step : forall (s : state Z)
                     (e e' e'' : expr)
                     (HStep : s |- e --> e')
                     (Heval: s |- e' -->> e''), s |- e -->> e''
  where "st |- e -->> e'"  := (ss_eval st e e').

  #[export] Hint Constructors ss_eval.

  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof. 
    inv HV. intro. intro. inv H. inv H0.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. 
    assert (normal_form ((Nat 10) [\/] (Nat 20))) as NF. 
    { intro. intro. inv H. inv H0.
      * inv LEFT.
      * inv RIGHT.
      * inv EVAL. inv VALA. inv VALB. inv BOOLA. }
    intro.
    remember (H ((Nat 10) [\/] (Nat 20)) NF).
    inv i.
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. 
    intro. 
    remember (Var (Id 0)). remember (Var (Id 1)).
    remember (Nat Z.zero). remember (Nat Z.one).
    remember ([(Id 0, Z.zero); (Id 1, Z.one)] : state Z).
    remember (H (e [+] e0) (e1 [+] e0) (e [+] e2) s).
    assert ((s) |- e [+] e0 --> (e1 [+] e0)). 
    { constructor. rewrite Heqe1. rewrite Heqe. rewrite Heqs. constructor. constructor. }
    assert ((s) |- e [+] e0 --> (e [+] e2)). 
    { constructor. rewrite Heqe0. rewrite Heqe2. rewrite Heqs. 
      constructor. constructor. intuition. inversion H1. constructor. }
    remember (e3 H0 H1).
    inversion e4. subst. inversion H3. 
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. 
    inversion H1; inversion H2; subst. 
    all: try by (inversion H5; rewrite H0 in VAL0;
                remember (state_deterministic Z s i z z1 VAL VAL0); rewrite e; auto).
    - inversion H2; subst. inversion LEFT0. inversion RIGHT.
    - inversion H2; subst. inversion LEFT. inversion RIGHT0.
    - inversion H1; inversion H2. subst. 
      remember (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z1 EVAL1 EVAL2).
      rewrite e. reflexivity.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. 
    dependent induction e' generalizing e. 
    * constructor.
    * dependent induction Heval. remember (IHHeval i). auto.
    * dependent induction Heval. remember (IHHeval b e'1 e'2 IHe'1 IHe'2). auto.
  Qed.

  Lemma ss_bs_step (s : state Z)
                   (e e' : expr)
                   (z : Z)
                   (STEP : (s) |- e --> e')
                   (EXEC : [|e'|] s => z)
    : [|e|] s => (z).
  Proof.
    dependent induction e.
    all: try by (inv STEP; inv EXEC; auto).
    dependent induction b; 
    inv STEP; inv EXEC; eauto.
  Qed.

  Lemma ss_eval_equiv_bop (b : bop)
                          (e1 e2 : expr)
                          (s : state Z)
                          (za zb zc : Z)
                          (SS1 : ((s) |- e1 -->> (Nat za)))
                          (SS2 : ((s) |- e2 -->> (Nat zb)))
                          (EVAL : ([|Bop b e1 e2|] s => zc))
                          : ((s) |- (Bop b e1 e2) -->> (Nat zc)).
  Proof. admit. Admitted.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. 
    split; intro.
    { revert dependent z. 
      dependent induction e; try by (intro; intro; inv H; econstructor; eauto; eauto).
      intros z' H. 
      inv H; specialize (IHe1 _ _ VALA); specialize (IHe2 _ _ VALB);
      eapply ss_eval_equiv_bop; eauto; eauto; eassumption. }
    dependent induction H; auto.
    assert (Nat z = Nat z). { reflexivity. } remember (IHss_eval z H0). 
    remember (ss_bs_step s e e' z HStep e0).
    assumption.
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
  Proof. 
    dependent induction e.
    { reflexivity. }
    { unfold rename_expr. rewrite Hinv. reflexivity. }
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
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
    unfold renamings_inv in Hinv.
    destruct a, r, r'. simpl. rewrite -> IHst.
    assert (x (x0 i) = i). { auto. }
    rewrite -> H. reflexivity.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. 
    inv BH. inv H. intro. intro. congruence.
  Qed.
  
  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. admit. Admitted.
    
End Renaming.
