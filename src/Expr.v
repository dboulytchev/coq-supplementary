Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

Require Import Stdlib.Program.Equality.
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
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. 
    apply bs_Nat.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH.
    inversion VALB.
    replace (za*2)%Z with (za+za)%Z.
    apply bs_Add.
    + auto.
    + auto.
    + intuition.
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
  generalize dependent z; induction e; intros; inversion HSub; eauto; inversion HV; eauto.
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
  - inversion_clear RED. exists z. inversion ID.
    subst. apply VAR.
  - inversion_clear RED; inversion ID; subst; inversion H3; eauto.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros.
  pose proof (defined_expression e s z id).
  intro.
  pose proof (H H0 ID).
  inversion H1.
  specialize (UNDEF x).
  auto.
Qed.
(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z1.
  generalize dependent z2.
  induction e; intros.
  - inversion E2. inversion E1. lia.
  - inversion E2. inversion E1.
    apply state_deterministic with s i; auto.
  - inversion E1; subst; inversion E2; subst;
    specialize (IHe1 za0);
    apply IHe1 in VALA;
    specialize (IHe2 zb0);
    apply IHe2 in VALB.
    all: (try (rewrite VALA; rewrite VALB; subst);
          auto;
          try(subst; contradiction)).
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
  - inversion EV. subst. constructor.
  - specialize (FV i). inversion EV. unfold equivalent_states in FV. constructor. apply FV; auto.
    - inversion EV; subst.
      all: (try econstructor;
            try eauto;
            try eapply IHe1;
            try eapply IHe2;
            try eauto;
            try intros;
            try eapply FV;
            try econstructor;
            try eauto).
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl' (e : expr): e ~~ e.
Proof.
  constructor.
  all: eauto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  constructor;
  unfold equivalent in EQ;
  specialize (EQ n s);
  destruct EQ;
  auto.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  constructor;
  unfold equivalent in EQ1;
  unfold equivalent in EQ2;
  specialize (EQ1 n s);
  specialize (EQ2 n s);
  destruct EQ1;
  destruct EQ2;
  eauto.
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
  split; intros H.
  - intros C; induction C; simpl; [exact H | | ]; split; intros; inversion H0; econstructor; eauto; now apply IHC.
  - apply (H Hole).
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
    induction HE; eauto.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z) as ez.
    induction HR.
    - destruct e; try apply discriminate. apply se_Stop.
      + rewrite -> Heqez. eauto.
      + rewrite -> Heqez. eauto.
    - apply se_Step with e'.
      + eauto.
      + apply IHHR. 
        eauto.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.
  
  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof.
   induction H1. 
   - destruct e''; inversion_clear H2.
   - apply se_Step with e'; eauto.
  Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1.
    - trivial.
    - eauto.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    inversion HV; subst.
    unfold normal_form.
    intros.
    intro H.
    inversion H.
    inversion H0.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intro H.
    specialize (H (Nat 322 [/] Nat 0)).
    assert (N0: normal_form (Nat 322 [/] Nat 0)).
      {
        intro. intro. inversion H0; subst.
        inversion H1; subst.
          - inversion LEFT.
          - inversion RIGHT.
          - inversion EVAL; subst.
            inversion VALB; subst.
            intuition.
      }
    apply H in N0.
    inversion N0.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. 
    intro H.
    remember ((Nat 1) [+] (Nat 0)) as e1.
    remember ((Nat 1) [+] (Nat 1)) as e2.
    specialize (H (e1 [+] e2) (Nat (1 + 0) [+] e2) (e1 [+] (Nat (1 + 1))) (List.nil)).
    
    assert (H1: [|e1|] ([]) => (1 + 0)) by (subst; apply bs_Add; apply bs_Nat).
    assert (H2: [|e2|] ([]) => (1 + 1)) by (subst; apply bs_Add; apply bs_Nat).
    
    assert (H3: ([]) |- e1 [+] e2 --> (Nat (1 + 0) [+] e2)) by 
      (apply ss_Left; rewrite Heqe1; apply ss_Bop; auto).
    
    assert (H4: ([]) |- e1 [+] e2 --> (e1 [+] Nat (1 + 1))) by
      (apply ss_Right; rewrite Heqe2; apply ss_Bop; auto).
    
    apply H in H3; [subst; inversion H3 | exact H4].
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst; inversion H2; subst; auto.
    - assert (z = z0) by (apply state_deterministic with s i; [exact VAL | exact VAL0]).
      congruence.
    - inversion LEFT.
    - inversion RIGHT.
    - assert (z = z0) by (eapply eval_deterministic; [exact EVAL | exact EVAL0]).
      congruence.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval. 
    all: try econstructor. 
    all: eauto. 
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction C; try (simpl; induction IHC); eauto.
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    eapply ss_reachable_trans.
    - apply ss_subst with (C := BopL op Hole e2). 
      eauto.
    - apply ss_subst with (C := BopR op e1' Hole). 
      eauto.
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    inversion H; 
    subst;
    specialize (eval_deterministic e1 s za za0 VALA VALA0) as ->;
    specialize (eval_deterministic e2 s zb zb0 VALB VALB0) as ->;
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
    apply ss_eval_reachable in IHe1.
    apply ss_eval_reachable in IHe2.
    apply ss_reachable_trans with (Bop op (Nat za) (Nat zb)).
    apply ss_subst_binop; auto.
    apply ss_bop_reachable with e1 e2; auto.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    split.
    - intros; induction H; eauto.
    - intros.
      generalize dependent z.
      induction e.
      + intros.
        inversion H; subst.
        * eauto.
        * inversion HStep.
      + intros.
        inversion H; subst.
        inversion HStep; subst.
        inversion Heval; subst.
        * eauto.
        * inversion HStep0.
      + intros.
        assert (exists zl zr, s |- e1 -->> (Nat zl) /\ s |- e2 -->> (Nat zr) /\ [|Bop b (Nat zl) (Nat zr)|] s => z).
        { clear IHe1 IHe2.
          remember (Bop b e1 e2).
          remember (Nat z).
          generalize dependent e2.
          generalize dependent e1.
          induction H; intros.
          - inversion Heqe.
          - specialize (IHss_eval Heqe0).
            inversion HStep; subst.
            * inversion H1.
            * specialize (IHss_eval l' e2).
              inversion H1; subst.
              assert (Bop b l' e2 = Bop b l' e2) by reflexivity.
              specialize (IHss_eval H0).
              destruct IHss_eval as [zl [zr [R1 [R2 R3]]]].
              exists zl, zr.
              eauto.
            * specialize (IHss_eval e1 r').
              inversion H1; subst.
              assert (Bop b e1 r' = Bop b e1 r') by reflexivity.
              specialize (IHss_eval H0).
              destruct IHss_eval as [zl [zr [R1 [R2 R3]]]].
              exists zl, zr.
              eauto.
            * inversion H1; subst.
              exists zl, zr.
              split; try apply se_Stop.
              split; try apply se_Stop.
              inversion H; subst.
              -- assumption.
              -- inversion HStep0.
        }
        destruct H0 as [zl [zr [H1 [H2 H3]]]].
        specialize (IHe1 zl H1).
        specialize (IHe2 zr H2).
        inversion H3; inversion VALA; inversion VALB; subst; eauto.
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
    inversion H1;
    inversion H2;
    subst;
    eauto.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof.
    inversion H1;
    inversion H2;
    subst;
    eauto.
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

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    intros.
    inversion HT; inversion HVal; subst.
    all: try (inversion H0; subst; unfold zbool; eauto).
    all: try (inversion BOOLA; inversion BOOLB; subst; eauto).
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
    destruct r.
    destruct b.
    destruct a.
    exists (exist _ x0 (ex_intro _ _ (conj e0 e))).
    unfold renamings_inv; simpl; auto.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r, b, a.
    assert (B: Bijective x0).
    - unfold Bijective. 
      exists x. 
      split; auto.
    - exists (exist _ x0 B).
      unfold renamings_inv.
      intros. 
      auto.
  Qed.

  Lemma renaming_inv3 (r : renaming) : exists (r' : renaming), renamings_inv r' r /\ renamings_inv r r'.
  Proof.
    destruct r as [f BH].
    destruct BH as [f' [Hbij Hinv]].
    assert (BH': Bijective f').
    { unfold Bijective. exists f. auto. }
    exists (exist _ f' BH').
    unfold renamings_inv.
    split.
    exact Hbij.
    exact Hinv.
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
    induction e; simpl; auto.
    - rewrite Hinv; auto.
    - rewrite IHe1, IHe2; auto.
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
    destruct r, r'.
    f_equal.
    destruct a.
    simpl.
    assert (x (x0 i) = i).
    apply (Hinv i).
    rewrite H.
    rewrite IHst.
    trivial.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    destruct BH, H.
    intro.
    intros.
    rewrite <- (H x0).
    rewrite H1.
    trivial.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
  assert (rename_simpl :
            forall (r0 : renaming) (st0 : state Z) (i : id) (x : Z),
              rename_state r0 ((i, x) :: st0) =
              (rename_id r0 i, x) :: rename_state r0 st0).
  { intros [f BH] st0 i x; unfold rename_state, rename_id; reflexivity. }
  assert (rename_equiv' :
            forall (r0 : renaming) (st0 : state Z) (x0 : id) (z0 : Z),
              st0 / x0 => z0 -> (rename_state r0 st0) / rename_id r0 x0 => z0).
  { intros r0 st0 x0 z0 Hbind; induction Hbind.
    - rewrite rename_simpl; constructor.
    - rewrite rename_simpl; constructor.
      + destruct r0 as [f [f' [Hbij Hinv]]]; unfold rename_id; congruence.
      + assumption. }
  assert (rename_equiv :
            forall (r0 : renaming) (st0 : state Z) (x0 : id) (z0 : Z),
              st0 / x0 => z0 <-> (rename_state r0 st0) / rename_id r0 x0 => z0).
  { intros r0 st0 x0 z0; split; intro H.
    - now apply rename_equiv'.
    - pose proof (renaming_inv3 r0) as [r' [Hinv Hinv']].
      rewrite <- (re_rename_state r' r0 Hinv st0) in *.
      rewrite (re_rename_state r0 r' Hinv' (rename_state r0 st0)) in H.
      rewrite <- (Hinv x0) in *.
      rewrite (Hinv' (rename_id r0 x0)) in H.
      eapply rename_equiv'.
      exact H. }
  split.
  - intros Hev; induction Hev; econstructor; eauto.
  - intros Hev.
    remember (rename_state r st) as st'.
    remember (rename_expr r e) as e'.
    generalize dependent z.
    generalize dependent e'.
    generalize dependent st'.
    induction e; intros.
    + subst; inversion Hev; subst; constructor; auto.
    + subst; inversion Hev; subst.
      apply rename_equiv in VAR; eauto.
    + specialize (IHe1 (rename_state r st) eq_refl (rename_expr r e1) eq_refl).
      specialize (IHe2 (rename_state r st) eq_refl (rename_expr r e2) eq_refl).
      assert (rename_expr r e2 = rename_expr r e2) by reflexivity.
      assert (e' = Bop b (rename_expr r e1) (rename_expr r e2)).
      { unfold rename_expr in *. exact Heqe'. }
      rewrite H0 in Hev; inversion Hev;
      subst; eauto.
  Qed.
End Renaming.
