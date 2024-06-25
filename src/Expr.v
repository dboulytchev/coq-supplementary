Require Import FinFun.
Require Import BinInt ZArith_dec.
From semantics Require Export Id.
From semantics Require Export State.
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
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. inversion HH. inversion VALB. assert ((za * 2)%Z = (za + za)%Z).
    lia. rewrite H. apply bs_Add; assumption.
  Qed.

End SmokeTest.

(* A relation of one expression being a subexpression of another *)
Reserved Notation "e1 << e2" (at level 0).

Inductive subexpr : expr -> expr -> Prop :=
  subexpr_refl : forall e : expr, e << e
| subexpr_left : forall e e' e'' : expr, forall op : bop, e << e' -> e << (Bop op e' e'')
| subexpr_right : forall e e' e'' : expr, forall op : bop, e << e'' -> e << (Bop op e' e'')
where "e1 << e2" := (subexpr e1 e2).

Lemma strictness (e e' : expr) (HSub : e' << e) (st : state Z) (z : Z) (HV : [| e |] st => z) :
  exists z' : Z, [| e' |] st => z'.
Proof. generalize dependent z. induction HSub; intros z Heevz.
  { exists z. assumption. }
  { inversion Heevz; subst op; apply IHHSub in VALA; assumption. }
  { inversion Heevz; subst op; apply IHHSub in VALB; assumption. }
Qed.

Reserved Notation "x ? e" (at level 0).

(* Set of variables in an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (a b : expr) (op : bop), id ? a \/ id ? b -> id ? (Bop op a b)
where "x ? e" := (V e x).

(* If an expression is defined in some state, then each of its variables is
   defined in that state
 *)      
Lemma defined_expression
      (e : expr) (s : state Z) (z : Z) (id : id)
      (RED : [| e |] s => z)
      (ID  : id ? e) :
  exists z', s / id => z'.
Proof.
  generalize dependent z. induction e; intros z0 H.
  { inversion ID. }
  { inversion ID. inversion H. subst. exists z0. assumption. }
  { inversion ID. subst. destruct H4 as [Hide1|Hide2].
    - inversion H; subst; apply IHe1 with (z:=za); auto.
    - inversion H; subst; apply IHe2 with (z:=zb); auto. }
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined in that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  induction e; inversion ID; subst; intros z H.
  { apply defined_expression with (id:=id) in H; [ |assumption].
    destruct H as [z' is_def]. apply UNDEF in is_def. contradiction. }
  { destruct H3 as [Hide1|Hide2]. 
    - inversion_clear H; apply IHe1 with (z:=za); auto.
    - inversion_clear H; apply IHe2 with (z:=zb); auto. }
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. generalize dependent z2. generalize dependent z1.
  induction e; intros z1 Hevz1 z2 Hevz2.
  { inversion Hevz1. inversion Hevz2. intuition. }
  { inversion Hevz1. inversion Hevz2. subst.
    apply state_deterministic with (st:=s) (x:=i); assumption. }
  { inversion Hevz1; subst; inversion Hevz2; subst;
    (* normal Ops *)
    specialize IHe1 with (z1:=za) (z2:=za0);
    specialize IHe2 with (z1:=zb) (z2:=zb0); intuition;
    (* divisions *)
    try (subst; reflexivity);
    (* bools *)
    rewrite H1 in OP; rewrite H in OP; contradiction. }
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

Lemma eq_st2 : forall (b: bop) (e1 e2: expr) (s1 s2 : state Z),
  (forall (id : id), id ? (Bop b e1 e2) -> (equivalent_states s1 s2 id)) -> 
  (forall (id : id), id ? e1 -> (equivalent_states s1 s2 id)) /\
  (forall (id : id), id ? e2 -> (equivalent_states s1 s2 id)).
Proof.
  intros b e1 e2 s1 s2 Hboth. split;
  intros id ide; apply Hboth; apply v_Bop; intuition.
Qed.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
  generalize dependent z. induction e; intros z0 EV.
  { inversion EV. intuition. }
  { inversion EV. specialize FV with (id:=i).
    specialize v_Var with (id:=i) as H. apply FV in H.
    unfold equivalent_states in H. apply H in VAR. intuition. }
  { apply eq_st2 in FV as [He1 He2]. inversion EV;
      try (
        apply IHe1 with (z:=za) in He1; [ |assumption];
        apply IHe2 with (z:=zb) in He2 ; [ |assumption];
        econstructor; try apply He1 ; try apply He2; try apply OP);
      try assumption. }
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. unfold equivalent. reflexivity. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. unfold equivalent in *. symmetry. apply EQ. Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. unfold equivalent in *. intros n s. transitivity ([|e2|] s => n); auto.
Qed.

Add Parametric Relation : expr equivalent
  reflexivity proved by eq_refl
  symmetry proved by eq_symm
  transitivity proved by eq_trans
  as program_equivalence.

From Coq Require Import Setoid.

Add Morphism equivalent
    with signature equivalent ==> eq ==> iff
    as equivalent_mor.
Proof.
  intros x y Heq y0. split.
  { intros H. apply eq_symm in Heq. apply eq_trans with (e2:= x); auto. }
  { intros H. apply eq_trans with (e2:= y); auto. }
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
  unfold contextual_equivalent. split.
  - intros H. induction C.
    { simpl. apply H. }
    { simpl. split; intros; inversion H0; apply IHC in VALA;
      econstructor; eauto. }
    { simpl. split; intros; inversion H0; apply IHC in VALB;
      econstructor; eauto. }
  - intros H. specialize H with (C:=Hole). simpl in H. apply H.
Qed.

Module SmallStep.

  Inductive is_value : expr -> Prop :=
    isv_Intro : forall n, is_value (Nat n).
               
  Reserved Notation "st |- e --> e'" (at level 0, e at next level, e' at next level).

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

  Reserved Notation "st |- e -->> e'" (at level 0, e at next level, e' at next level).

  Inductive ss_eval : state Z -> expr -> expr -> Prop :=
    se_Stop : forall (s : state Z)
                     (z : Z),  (s |- (Nat z) -->> (Nat z))
  | se_Step : forall (s : state Z)
                     (e e' e'' : expr)
                     (HStep : (s |- e --> e'))
                     (Heval: (s |- e' -->> e'')), (s |- e -->> e'')
  where "st |- e -->> e'"  := (ss_eval st e e').
  
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    intros s [e' He']. inversion HV. destruct H. inversion He'.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intros H. specialize H with (Nat 1 [/] Nat 0). assert (HNorm : normal_form ((Nat 1) [/] (Nat 0))).
    { intros st [e' He']. inversion He'.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL.
        specialize eval_deterministic with (e := Nat 0)
        (s := st) (z1:=0%Z) (z2:=zb) as contra. assert ([|Nat 0|] st => 0).
        + auto. 
        + intuition. }
    { apply H in HNorm. inversion HNorm. }
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    intros H.
    remember ((Nat 1 [+] Nat 1)) as a.
    remember (Nat 2) as res.
    specialize H with (e:=(a [+] a)) (e':=(res [+] a)) (e'':=(a [+] res)) (s:=[]).
    assert ([] |- (a [+] a) --> (res [+] a)).
    { apply ss_Left. rewrite Heqa. rewrite Heqres. apply ss_Bop.
      imm_replace 2%Z (1 + 1)%Z. apply bs_Add; apply bs_Nat. }
    { apply H in H0.
      - injection H0. subst. intros H112. inversion H112.
      - apply ss_Right. subst. apply ss_Bop. imm_replace 2%Z (1 + 1)%Z.
        apply bs_Add; apply bs_Nat. }
  Qed.

Require Import Coq.Program.Equality.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. dependent destruction H1; dependent destruction H2.
  { specialize (state_deterministic _ _ _  _ _ VAL VAL0) as Heq. rewrite Heq. reflexivity. }
  { inversion H2. }
  { inversion H2. }
  { specialize (eval_deterministic _ _ _ _ EVAL EVAL0) as Heq. rewrite Heq. reflexivity. }
Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    dependent induction e' generalizing e.
    - constructor.
    - dependent induction Heval. apply (IHHeval i). reflexivity.
    - dependent induction Heval. apply (IHHeval b e'1 e'2); auto.
  Qed.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    split; intros H.
    - dependent destruction H.
      + constructor.
      + apply se_Step with (e':= Nat z).
        * constructor. assumption.
        * constructor.
      + apply se_Step with (e':=Nat(za+zb)).
        * 
  Admitted.
  
End SmallStep.

Module Renaming.
  
  Definition renaming := { f : id -> id | Bijective f }.
  
  Fixpoint rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.
Require Import Coq.Program.Equality.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.
  
  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof. destruct r as [f Hbij]. inversion Hbij.
    assert (Bijective x).
    * unfold Bijective. exists f. apply and_comm. assumption.
    * exists (exist Bijective x H0). destruct H. auto.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. destruct r as [f Hbij]. inversion Hbij.
    assert (Bijective x).
    * unfold Bijective. exists f. apply and_comm. assumption.
    * exists (exist Bijective x H0). destruct H. auto.
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
    dependent induction e.
    - reflexivity.
    - unfold rename_expr. rewrite Hinv. reflexivity.
    - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
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
    - destruct a as [id z]. destruct r', r. simpl. rewrite IHst.
      assert (x0 (x id) = id). auto. rewrite H. reflexivity.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    inversion BH. destruct H as [H1 H2].
    unfold Injective. intros x0 y H. specialize H2 with (y:=(f x0)) as H3.
    specialize H1 with (x:=x0) as H4. rewrite H in H4. rewrite <- H4. apply H1.
  Qed.
  
  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    
  Admitted.
    
End Renaming.
