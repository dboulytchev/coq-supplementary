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
  
    Lemma zero_always_neg : ~ (forall x s, [| Var x [*] Nat 0 |] s => Z.zero).
    Proof.
      unfold not. intros zero_always.
      specialize zero_always with (Id 0) [].
      inversion zero_always. 
      inversion VALA. apply st_eval_binds in VAR. unfold st_eval in VAR. discriminate.
    Qed.

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    apply bs_Nat.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. 
    inversion HH. subst.
    assert ((za * 2)%Z = (za + za)%Z).
    { symmetry. apply (Zplus_diag_eq_mult_2 za). }
    subst. inversion VALB. subst. rewrite H. apply bs_Add.
      assumption.
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
  generalize dependent st.
  induction HSub; intros.
  
    exists z. assumption.
    
    inversion HV; subst.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
      apply IHHSub with za. assumption.
    
    inversion HV; subst.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
      apply IHHSub with zb. assumption.
Qed.

Reserved Notation "x ? e" (at level 0).

Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (a b : expr) (op : bop), id ? a \/ id ? b -> id ? (Bop op a b)
where "x ? e" := (V e x).

#[export] Hint Constructors V : core.

   
Lemma defined_expression
      (e : expr) (s : state Z) (z : Z) (id : id)
      (RED : [| e |] s => z)
      (ID  : id ? e) :
  exists z', s / id => z'.
Proof. 
  generalize dependent z.
  
  induction e.
  
  intros. inversion ID.
  
  intros. inversion ID. subst. 
    inversion RED. subst. 
    exists z. exact VAR.
  
  intros. inversion RED. 
    all: subst. 
    all: inversion ID. subst.
    all: inversion H3. 
    all: eauto.
Qed.

Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z0 H.
  
  assert (exists z', s / id => z').
  { eapply defined_expression; eauto. }
  
  destruct H0 as [z' H0].
  apply (UNDEF z'). assumption.
Qed.

Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z1. generalize dependent z2.
  induction e; intros.
  
  inversion E1; subst. inversion E2; subst. reflexivity.
  
  inversion E1; subst. inversion E2; subst.
    apply (state_deterministic Z s i z1 z2); assumption.
  
  inversion E1; subst; inversion E2; subst; try solve [
      specialize (IHe1 za0 VALA0 za VALA);
      specialize (IHe2 zb0 VALB0 zb VALB);
      subst; reflexivity |
      specialize (IHe1 za0 VALA0 za VALA);
      specialize (IHe2 zb0 VALB0 zb VALB);
      subst; contradiction
    ].
Qed.

Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
  Proof. 
    revert EV. revert z. induction e; intros.
      inversion EV. apply bs_Nat.
      inversion EV. remember (v_Var i).
        remember (FV i v). 
        remember (e z). destruct i1.
        remember (s0 VAR).
        apply (bs_Var). assumption.
      assert ((forall id : id, (id) ? (e1) -> equivalent_states s1 s2 id)).
        { intros.
          assert ((id) ? (Bop b e1 e2)) as IDDF.
          { constructor. auto. }
          specialize (FV id IDDF).
          assumption. }
        specialize (IHe1 H).
        assert ((forall id : id, (id) ? (e2) -> equivalent_states s1 s2 id)).
        { intros.
          assert ((id) ? (Bop b e1 e2)) as IDDF.
          { constructor. auto. }
          specialize (FV id IDDF).
          assumption. }
        specialize (IHe2 H0).
        inversion EV;
        specialize (IHe1 za VALA); specialize (IHe2 zb VALB);
        econstructor; eassumption.
  Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. constructor. 
  auto.
  auto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent in *.
  intros n s.
  specialize (EQ n s).
  apply iff_sym.
  assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
  Proof.
    unfold equivalent in *.
    intros n s.
    specialize (EQ1 n s).
    specialize (EQ2 n s).
    apply iff_trans with ([| e2 |] s => n); assumption.
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
    constructor; intros.
    constructor.
      revert H. revert n.
        induction C.
        intros. simpl. simpl in H0.
          specialize (H n s). destruct H. apply (H H0).
        intros. simpl. simpl in H0.
          inversion H0; econstructor;
              specialize (IHC za H VALA);
              eassumption;
              assumption.
        intros. simpl. simpl in H0.
          inversion H0.
            constructor. assumption. apply (IHC zb H VALB).
            constructor. assumption. apply (IHC zb H VALB).
            constructor. assumption. apply (IHC zb H VALB).
             constructor. assumption. apply (IHC zb H VALB). assumption.
             constructor. assumption. apply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption. assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption. assumption.
      revert H. revert n. induction C.
        intros. simpl. simpl in H0.
          specialize (H n s). destruct H. apply (H1 H0).
        intros. simpl. simpl in H0.
          inversion H0; econstructor;
              specialize (IHC za H VALA);
              eassumption;
              assumption.
        intros. simpl. simpl in H0.
          inversion H0.
             constructor. assumption. apply (IHC zb H VALB).
             constructor. assumption. apply (IHC zb H VALB).
             constructor. assumption. apply (IHC zb H VALB).
             constructor. assumption. apply (IHC zb H VALB). assumption.
             constructor. assumption. apply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption. assumption.
             econstructor. eassumption. eapply (IHC zb H VALB). assumption. assumption.
    specialize (H (Hole)). simpl in H. assumption.
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
    apply reach_base. 
    apply reach_step with (e' := e') (e'' := e''); assumption.  
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof. remember (Nat z). induction HR.
    subst. apply se_Stop. 
    subst. eapply se_Step.
      eauto.
      eauto.
    Qed.
  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.
  
  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
    Proof. induction H1.
      inversion H2.
      econstructor.
        eauto.
        eauto. 
    Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
    Proof.
      induction H1.
      assumption.
      apply IHss_reachable in H2.
        apply reach_step with (e := e) (e' := e'); assumption.
    Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    unfold normal_form.
    intros s [e' H].
    inversion HV. subst.
    inversion H; subst.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
    unfold normal_form.
    unfold not. intros.
    assert (NF: is_value (Nat 42 [/] Nat 0)).
    apply H. intros. inversion H0. inversion H1; subst.
      inversion LEFT. 
      inversion RIGHT. 
      inversion EVAL. subst. inversion VALB. subst. contradiction. 
    inversion NF. 
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    intro H.
    set (x := Id 0).
    set (s := [(x, Z.one)] : state Z). 
    set (e := Bop Add (Var x) (Var x)).
    set (e1 := Bop Add (Nat Z.one) (Var x)).
    set (e2 := Bop Add (Var x) (Nat Z.one)).
    assert (H1: s |- e --> e1).
    {
      unfold e, e1, s, x.
      apply ss_Left.
      apply ss_Var.
      apply st_binds_hd. 
    }
    assert (H2: s |- e --> e2).
    {
      unfold e, e2, s, x.
      apply ss_Right.
      apply ss_Var.
      apply st_binds_hd. 
    }
    assert (H_diff: e1 <> e2).
    {
      unfold e1, e2.
      intro Heq.
      injection Heq as Heq1 Heq2.
      discriminate Heq1.
    }
    specialize (H e e1 e2 s H1 H2).
    contradiction.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst. 
      inversion H2; subst.
       remember (state_deterministic Z s i z z0 VAL VAL0).
       subst. reflexivity. 
      inversion H2; subst.
        inversion LEFT.  
        inversion RIGHT. 
        remember (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z0 EVAL EVAL0).
         subst. reflexivity. 
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. 
    induction Heval.
      constructor. 
      apply IHHeval.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof. 
    induction C.
    eauto. 
    simpl. induction IHC.
     eauto. 
     eauto. 
     simpl. induction IHC.
     eauto. 
     eauto. 
  Qed.
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
    Proof.
      induction HR1; induction HR2.
      apply reach_base.
      apply reach_step with (e' := Bop op e e').
        apply ss_Right. assumption.
        assumption.
      apply reach_step with (e' := Bop op e' e0).
        apply ss_Left. assumption.
        assumption.
      apply reach_step with (e' := Bop op e' e0).
        apply ss_Left. assumption.        
        assumption. 
    Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
    Proof. 
      inversion H; subst; simpl;
      specialize (eval_deterministic e1 s za za0 VALA VALA0);
      specialize (eval_deterministic e2 s zb zb0 VALB VALB0);
      simpl; intros; subst; eauto.
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
    apply ss_reachable_eval.
    eauto.
    specialize (ss_subst_binop s e1 e2 (Nat za) (Nat zb) op IHe1 IHe2). intro.
    specialize (ss_bop_reachable s e1 e2 op za zb z H VALA VALB). intro.
    apply (ss_reachable_trans s (Bop op e1 e2) (Bop op (Nat za) (Nat zb)) (Nat z)).
    eauto.
    eauto.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
    Proof. 
    assert (HR: forall e s z, [| e |] s => z -> (s |- e -->> (Nat z))).
    { clear e. clear s. clear z. intros. generalize dependent z. induction e; intros z0 H.
      inversion H. apply se_Stop.
      inversion H. rewrite <- H2 in *. apply se_Step with (Nat z). apply ss_Var. assumption. apply se_Stop.
      inversion H; apply ss_eval_binop with za zb;
        solve
        [ apply IHe1; assumption
        | apply IHe2; assumption 
        | congruence ]. }
    split. 
    apply HR.
    intros. dependent induction H.
      constructor.
      specialize IHss_eval with z. assert (H1: Nat z = Nat z). { reflexivity. }
        apply IHss_eval in H1. clear IHss_eval.
        generalize dependent z.
        dependent induction HStep; intros; subst.
        inversion H1; subst. constructor. assumption.
        inversion H1; apply IHHStep in VALA; 
          try solve [apply HR in VALA; assumption];
          apply_eval za zb; assumption.
        inversion H1; apply IHHStep in VALB; 
          try solve [apply HR in VALB; assumption];
          apply_eval za zb; assumption.
        inversion H1; subst. assumption.
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
  Proof. destruct t1; destruct t2; inversion H1; inversion H2; eauto. Qed.
  
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

  Lemma type_preservation_neg : ~ (forall e e' t t' st (HS: t' << t) (HT: e :-: t) (HR: st |- e ~~> e'), e' :-: t'). 
  Proof.
    unfold not. 
    intros.
    specialize H with (Var (Id 0)) (Var (Id 0)) Int Bool [].
    assert (HSubt: Bool << Int). apply subt_base.
    apply H in HSubt.
    inversion HSubt.
    apply type_X.
    apply reach_base.    
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    intros.
    dependent induction HT.
    {inversion HVal. subst. right. eauto. }
    {inversion HVal. subst. left. eauto. }
    {inversion HVal. {left. eauto. } {right. eauto. } }
    {inversion HVal. {left. eauto. } {right. eauto. } }
    {inversion HVal. {left. eauto. } {right. eauto. } }
    {inversion HVal. {left. eauto. } {right. eauto. } }
    {inversion HVal. {left. eauto. } {right. eauto. } }
    {inversion HVal. {left. eauto. } {right. eauto. } }
    {inversion HVal. inversion BOOLA; inversion BOOLB; subst; eauto. }
    {inversion HVal. inversion BOOLA; inversion BOOLB; subst; eauto. }
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
    destruct r as [f biect].
    destruct biect as [g revr].
    assert (Bijective g).
    {
      exists f. split.
      intros. apply (proj2 revr).
      intros. apply (proj1 revr).
    }
    exists (exist _ g H).
    unfold renamings_inv, rename_id.
    intros.
    destruct revr as [revl revr'].
    apply revl.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r. inversion b. inversion H.
    assert (B: Bijective x0). { unfold Bijective. exists x. split; assumption. }
    exists (exist _ x0 B). unfold renamings_inv. intros. simpl. eauto.
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
      simpl. reflexivity.
      simpl.
      unfold renamings_inv in Hinv.
      rewrite Hinv.
      reflexivity.
      simpl.
      rewrite IHe1.
      rewrite IHe2.
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
    unfold renamings_inv in Hinv. induction st.
    eauto.
    destruct a, r, r'. simpl. rewrite IHst, Hinv. eauto.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    unfold Bijective in BH.
    unfold Injective.
    destruct BH as [g [Hgf Hfg]].
    intros x y Heq.
    apply (f_equal g) in Heq.
    rewrite !Hgf in Heq.
    assumption.
  Qed.
  
  Lemma eval_renaming_invariance_helper (e : expr) (st : state Z) (z : Z) (r : renaming) :
    [| e |] st => z -> [| rename_expr r e |] (rename_state r st) => z.
  Proof. 
    intro. generalize st z r H. clear H r z st. induction e; intros; inversion H; clear H.
    apply bs_Nat.
    apply bs_Var. subst. induction VAR; destruct r.
      apply st_binds_hd.
      apply st_binds_tl; simpl.
        intro. remember (bijective_injective x0 b). assert (id = id'). apply i. 
        exact H0. 
        contradiction.
        exact IHVAR.
    apply bs_Add. apply IHe1. exact VALA. apply IHe2. exact VALB.
    apply bs_Sub. apply IHe1. exact VALA. apply IHe2. exact VALB.
    apply bs_Mul. apply IHe1. exact VALA. apply IHe2. exact VALB.
    apply bs_Div. apply IHe1. exact VALA. apply IHe2. exact VALB. exact NZERO.
    apply bs_Mod. apply IHe1. exact VALA. apply IHe2. exact VALB. exact NZERO.
    apply bs_Le_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Le_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Lt_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Lt_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Ge_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Ge_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Gt_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Gt_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Eq_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Eq_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Ne_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_Ne_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    apply bs_And. apply IHe1. exact VALA. apply IHe2. exact VALB. exact BOOLA. exact BOOLB.
    apply bs_Or. apply IHe1. exact VALA. apply IHe2. exact VALB. exact BOOLA. exact BOOLB.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
    Proof. 
      split; intro.
      apply eval_renaming_invariance_helper. exact H.
      destruct (renaming_inv r).
        assert ([|rename_expr x (rename_expr r e)|] (rename_state x (rename_state r st)) => z). 
        apply eval_renaming_invariance_helper. exact H.
        assert (rename_expr x (rename_expr r e) = e).
          apply re_rename_expr. exact H0.
          assert (rename_state x (rename_state r st) = st).
            apply re_rename_state. 
            exact H0.
            rewrite -> H2 in H1. rewrite -> H3 in H1. exact H1.
    Qed.
End Renaming.
