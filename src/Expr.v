From Bignums Require Export BigZ.
Require Export Id.
Require Export State.

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

Hint Constructors eval.

Module SmokeTest.

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. 
    apply (bs_Nat). 
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion_clear HH.
    inversion_clear VALB.
    assert ((za * 2%Z)%Z = (za + za)%Z). { omega. }
    rewrite H.
    apply bs_Add.
    assumption. assumption.
  Qed.

End SmokeTest.

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
  induction e as [ | | Iop e0 IHe0 e1 IHe1].
  - intros. inversion ID.
  - intros. inversion_clear RED.
    assert (id = i) as EqI. 
    { inversion ID. reflexivity. }
    rewrite EqI. exists z. assumption.
  - inversion_clear ID.
    destruct H.
    + intros.
      inversion_clear RED; apply (IHe0 H za VALA).
    + intros.
      inversion_clear RED; apply (IHe1 H zb VALB).
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. 
  intro z.
  unfold not.
  remember (defined_expression e s z id) as Eq.
  intro H.
  pose proof (Eq H ID).
  inversion H0.
  specialize (UNDEF x).
  auto.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. 
  generalize dependent z2.
  generalize dependent z1.
  induction e ; intros.
  - assert (z = z1) as H1. { inversion E1. reflexivity. }
    assert (z = z2) as H2. { inversion E2. reflexivity. }
    subst. reflexivity.
  - inversion_clear E1. inversion_clear E2.
    apply (state_deterministic Z s i) ; assumption.
  - destruct b; 
      inversion_clear E1; inversion_clear E2; 
      specialize (IHe1 za VALA za0 VALA0); specialize (IHe2 zb VALB zb0 VALB0);
      try (subst; reflexivity).
    
      all: (rewrite IHe1 in OP; rewrite IHe2 in OP; contradict OP; auto).
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 / id => z <-> s2 / id => z.

Lemma eq_states_destruction (s1 s2 : state Z) (e1 e2 : expr) (op : bop) :
  (forall (id0 : id), (id0) ? (Bop op e1 e2) -> equivalent_states s1 s2 id0) ->
  (forall (id1 : id), (id1) ? (e1) -> equivalent_states s1 s2 id1) /\
  (forall (id2 : id), (id2) ? (e2) -> equivalent_states s1 s2 id2).
Proof.
  unfold equivalent_states.
  intro H.
  split;
    intros id1 H1 z;
    specialize (H id1).
  - assert (id1 ? (Bop op e1 e2)) as UP. { apply v_Bop. auto. }
    specialize (H UP z). auto.
  - assert (id1 ? (Bop op e1 e2)) as UP. { apply v_Bop. auto. }
    specialize (H UP z). auto. 
Qed.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof. 
  generalize dependent z.
  induction e ; intros.
  - inversion EV. auto.
  - inversion_clear EV. specialize (FV i (v_Var i)).
    unfold equivalent_states in FV. specialize (FV z).
    inversion FV. auto.
  - destruct b;
      inversion_clear EV;
      apply (eq_states_destruction s1 s2 e1 e2) in FV;
      destruct FV as [FV0 FV1];
      specialize (IHe1 FV0 za VALA); specialize (IHe2 FV1 zb VALB).
    
    all: try (constructor; assumption; assumption).
    all: eauto.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  unfold equivalent.
  intros n s.
  tauto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. 
  unfold equivalent.
  unfold equivalent in EQ.
  intros n s.
  induction e1 ; induction e2 ; symmetry.
  all: apply (EQ n s).
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent.
  unfold equivalent in EQ1.
  unfold equivalent in EQ2.
  
  intros n s.
  specialize (EQ1 n s).
  specialize (EQ2 n s).
  transitivity ([|e2|] s => (n)).
  assumption. assumption.
Qed.

Inductive Context : Type :=
| Hole : Context
| BopL : bop -> Context -> expr -> Context
| BopR : bop -> expr -> Context -> Context.

Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | BopL b C e1 => Bop b (plug C e) e1
  | BopR b e1 C => Bop b (plug C e) e1
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

Definition contextual_equivalent (e1 e2 : expr) : Prop :=
  forall (C : Context), (C <~ e1) ~~ (C <~ e2).
Notation "e1 '~c~' e2" := (contextual_equivalent e1 e2)
                            (at level 42, no associativity).


Lemma eq_subst (e1 e2 : expr) (c : Context) (z : Z) (s : state Z) :
  (c <~ e1) ~~ (c <~ e2) -> [|c <~ e1|] s => (z) -> [|c <~ e2|] s => (z).
Proof.
  intro H.
  intro A.
  destruct c; 
    simpl; simpl in A; simpl in H; 
    unfold equivalent in H; 
    specialize (H z s); destruct H; 
    auto.
Qed. 

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  unfold equivalent.
  unfold contextual_equivalent.
  split.
  - intros H c.
    induction c.
    + simpl. assumption.
    + simpl. 
      constructor;
        intro L; inversion_clear L.
      
      all: try (pose proof (eq_subst e1 e2 c za s IHc) as IHP; pose proof (IHP VALA) as IHPA).
      all: try (apply eq_symm in IHc; 
                pose proof (eq_subst e2 e1 c za s IHc) as IHP; pose proof (IHP VALA) as IHPA).
      all: try (constructor; assumption; assumption).
      all: eauto.
      
    + constructor;
        intro L; inversion_clear L.
      
      all: try (pose proof (eq_subst e1 e2 c za s IHc) as IHP; pose proof (IHP VALA) as IHPA).
      all: try (apply eq_symm in IHc; 
                pose proof (eq_subst e2 e1 c za s IHc) as IHP; pose proof (IHP VALA) as IHPA).
      all: try (constructor; assumption; assumption).
      all: destruct c; simpl; eauto; simpl; eauto.

  - intro H.
    intros n s.
    specialize (H Hole).
    simpl in H.
    specialize (H n s).
    assumption.
Qed.