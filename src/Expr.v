Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require State.
Export State.
Require Export Lia.

Require Import List.
Import ListNotations.

From hahn Require Import HahnBase.
Require Import Coq.Program.Equality.


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
  Proof.
  admit. Admitted.
(* нет, выражение может быть просто не вычислимо в данном контексте *)
  Type zero_always.

  Definition zero_always_type := forall (x : id) (s : state Z), [|Var x [*] Nat 0|] s => (Z.zero).

  Lemma not_zero_always : ~ zero_always_type.
  Proof.
  unfold zero_always_type.
  unfold not.
  intros.
  pose (Id 0) as x.
  pose (nil : state Z) as st.
  specialize (H x st).
  inversion H; subst.
  inversion_clear VALA.
  inversion_clear VAR.
  Qed.



  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. 
  constructor.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
  inversion HH.
  subst.
  inversion VALB.
  subst.
  replace (za * 2)%Z with (za + za)%Z.
  constructor.
  assumption.
  assumption.
  lia.
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
  generalize dependent HV.
  generalize dependent z.
  induction HSub as [e1 | e1 e2 e3 op e1_in_e2 pi| e1 e2 e3 op e1_in_e2 pi];
  intros z HV.
  - exists z. exact HV. 
  -
  inversion HV;
  subst;
  try (
    apply pi with (z:= za); 
    assumption
  ).
  -   
  inversion HV;
  subst;
  try (
    apply pi with (z:= zb); 
    assumption
  ).
Qed.
    
(* т е если выражение вычислимо то вычислимо и подвыражение *)


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
  generalize dependent RED.
  generalize dependent ID.
  generalize dependent z.

  induction e as [e1 | e1 |  e1 e2 e3 e4 e5 ];
  intros z r1 r2;
  inversion r1;
  subst. 
  - inversion r2. subst. exists z. apply VAR.
  - 
  destruct H3.
  + inversion r2;subst;
  try(apply e3 with (z:= za); assumption; assumption).
  + inversion r2;subst;
  try(apply e5 with (z:= zb); assumption; assumption).

Qed.
  


(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
unfold not.
intros z1 a1.
assert (Exy: exists z', s / id => z').
apply defined_expression with (e := e) (s := s) (z := z1) (id := id); assumption.
destruct Exy as [z' Hz'].
apply UNDEF in Hz'.
contradiction.
Qed.

Lemma fast_def_get (e1 e2 : expr) (s : state Z) (z2 : Z) (b : _) (P : Prop)
(E2 : [|Bop b e1 e2|] s => (z2)) (pp : forall z2 , [|e1|] s => (z2) -> P) : P.
Proof.
inversion E2; subst;
apply pp with (z2:=za);
assumption.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
generalize dependent E1.
generalize dependent E2.
generalize dependent z1.
generalize dependent z2.
induction e;
try (
  intros z2 z1 E2 E1;
  inversion E1; inversion E2; subst;
  try (
    assert (G1: za = za0) by (apply IHe1 with (z1 := za) (z2 := za0); assumption; assumption);
    assert (G2: zb = zb0) by (apply IHe2 with (z1 := zb) (z2 := zb0); assumption; assumption);
    subst; reflexivity
  );
  reflexivity
).
-
intros z2 z1 E2 E1.
inversion E1; 
inversion E2; 
subst.
apply state_deterministic with (st:=s) (x := i).
assumption.
assumption.
-
intros z2 z1 E2 E1.
inversion E1; subst; inversion E2; subst;

assert (G1: za=za0) by (apply IHe1 with (z1:=za) (z2:=za0); assumption);
assert (G2: zb=zb0) by (apply IHe2 with (z1:=zb) (z2:=zb0); assumption);
subst; try lia; try contradiction.

Qed.




(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (key : id) (ID : key ? e),
          equivalent_states s1 s2 key)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
  generalize dependent z.
  generalize dependent FV.
  induction e;
  intros FV z1 a1.
  - inversion a1. subst. constructor.
  - inversion a1. subst. constructor. apply FV. constructor. assumption.
  - inversion a1; subst;
    try(constructor);
    try (ltac:(
      apply IHe1;
      [ intros key1 keyin; apply FV; constructor; auto
      | assumption ]
    ));
    try (ltac:(
      apply IHe2;
      [ intros key1 keyin; apply FV; constructor; auto
      | assumption ]
    ));
    try assumption;
    try(
    econstructor;
    [
      try (ltac:(
        apply IHe1;
        [ intros key1 keyin; apply FV; constructor; auto
        | eassumption ]
          ))
      |
      try (ltac:(
        apply IHe2;
        [ intros key1 keyin; apply FV; constructor; auto
        | eassumption ]
      ))
      | assumption

    ]).
Qed.
    

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. 
split; intro e1; apply e1.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
split;
intro a1;
apply EQ; assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
split;
  intro e.
  - 

  apply EQ2.
  apply EQ1.
  assumption.
  - 
  apply EQ1.
  apply EQ2.
  assumption.
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

(* Definition bop_eval (bop : bop) (v1 : option Z) (v2 : option Z) : option Z :=
  match v1, v2 with
  | Some v1, Some v2 => 
    match bop with
    | Add => Some (v1 + v2)
    | Sub => Some (v1 - v2)
    | Mul => Some (v1 * v2)
    | Div => Some (Z.div v1 v2)
    | Mod => Some (Z.modulo v1 v2)
    | Le  => Some (Z.one)
    | Lt  => Some (Z.one)
    | Ge  => Some (Z.one)
    | Gt  => Some (Z.one)
    | Eq  => Some (Z.one)
    | Ne  =>
    | And =>
    | Or  =>
    end
  | _, _ => None
  end. *)

(* Fixpoint expr_eval (e : expr) (st : state Z) : option Z :=
    match e with
    | Nat z => z
    | Var key => st_eval st key
    | Bop bop e1 e2 => bop_eval (expr_eval e1 st) (expr_eval e2 st)
    end. *)


Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  unfold contextual_equivalent, equivalent.
  split; intros.
  - generalize dependent n.
    induction C; intros; simpl.
    + split; apply H.
    + split; intros; inversion H0; subst; 
    try constructor; 
    try apply IHC in VALA; eauto.
    + split; intros; inversion H0; subst; 
    try constructor; 
    try apply IHC in VALB; eauto.
  -
  apply (H Hole).
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
  - constructor.
  - econstructor; eauto.
  Qed.


  (* Lemma ss_reachable_eval1 s e e1 (HR: s |- e ~~> e1) : s |- e -->> e1.
  Proof.
    remember (Nat z).
    induction HR.
    - subst. constructor.
    - subst. eauto.
  Qed. *)

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z).
    induction HR.
    - subst. constructor.
    - subst. eauto.
  Qed.
  

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.
  
  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof.
  induction H1; subst.
  - inversion H2.
  - apply (se_Step _ _ _ _ HStep). auto.
Qed.  

  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof. 
  induction H1.
  - assumption.
  - apply (reach_step _ _ _ _ HStep). auto.
  Qed.Require Import Coq.Program.Equality.

          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
  unfold normal_form.
  intros s e1.
  destruct e1.
  inversion H;subst;inversion HV. 
  Qed.

  Check (Var (Id 2)).


(* кастомная лемма для упрощения следующей *)
  Lemma negation_flipka {E} {P1} {P2} (e : E) (p1 : P1 e) (p2 : ~(P2 e)) : ~ forall (e : E), P1 e -> P2 e.
Proof.
  intro H.         
  apply p2.         
  apply H.          
  exact p1.
Qed.  

Lemma nolisnol {s} {zb} (VALB : [|Nat 0|] s => (zb)) : zb = (0)%Z.
Proof.
  inversion VALB. subst. auto.
Qed.

Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    pose ((Nat 1) [/] (Nat 0)) as kp.
    refine (negation_flipka kp _ _).
    - unfold normal_form.
      intros s.
      unfold not.
      intros a1.
      unfold kp in a1.
      inversion a1.
      destruct x.
      + inversion H. subst. inversion EVAL. apply nolisnol in VALB. subst.
      contradiction.
      + inversion H.
      + inversion H. subst.
        * inversion LEFT.
        * inversion RIGHT.
    - unfold not.
      intros iv.
      inversion iv.
  Qed.      


  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. 
  intro.
  pose (Var (Id 0)) as x.
  pose (x [+] x) as kp.
  pose ([(Id 0, 0%Z)]) as s.
  specialize (H
  kp
  ((Nat 0) [+] x)
  (x [+] (Nat 0))
  s
  ).
  discriminate H.
  - constructor. constructor. constructor.
  - constructor. constructor. constructor.
  Qed. 

  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
  inversion H1; subst.
  -
  inversion H2; subst.
  f_equal. eapply state_deterministic.
  + eauto.
  + eauto.
  -  
  inversion H2; subst.
  + inversion LEFT.
  + inversion RIGHT.
  + f_equal.
  eapply eval_deterministic; eauto.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - constructor.
    - auto.
  Qed.  

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
  induction C.
  - eauto.
  - simpl. induction IHC.
  + eauto.
  + eauto.
  - simpl. induction IHC.
  + eauto.
  + eauto.
  Qed. 
   
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
  pose (Bop op e1' e2) as mid.
  apply ss_reachable_trans with (e':=mid).
  - eapply ss_subst with (C := (BopL op Hole e2)).
  auto.
  - eapply ss_subst with (C := (BopR op e1' Hole)).
  auto.
  Qed.
  

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    inversion H;subst;
    specialize (eval_deterministic _ _ _ _ VALA VALA0 ) as p1;
    specialize (eval_deterministic _ _ _ _ VALB VALB0 ) as p2;
    subst; eauto.
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
    - apply ss_subst_binop; apply ss_eval_reachable; eauto.
    - eapply ss_bop_reachable; eauto.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.
  
Lemma pi_f (s : state Z)
            (e e' : expr)
            (z : Z)
            (a1: (s) |- e --> e')
            (a2: [|e'|] s => z) : [|e|] s => (z).
Proof.
dependent induction e.
    -inversion a1; subst.
    -inversion a1; subst; inversion a2; subst.
     auto.
    -inversion a1; subst; inversion a2; subst; eauto.
Qed.


  Lemma ss_eval_equiv_left (e : expr)(s : state Z)(z : Z) 
                  (H : s |- e -->> (Nat z)) 
                      : [| e |] s => z.
  Proof.
    dependent induction H.
    - eauto.
    - assert (pi : [|e'|] s => z).
    { eauto. }
    apply pi_f with (e':=e');eauto.
  Qed.



  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
  split.
  +
  generalize dependent z.
  induction e.
  - intros. inversion H;subst. eauto.
  - intros. inversion H;subst. eauto.
  - intros.
  inversion H;subst;
  apply ss_eval_binop with (za:= za) (zb:=zb);
  try assumption;
  try (apply IHe1; auto);
  try (apply IHe2; auto).
+ apply ss_eval_equiv_left.
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
  inversion H1;inversion H2; subst; eauto.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof.
  inversion H1; inversion H2; subst; eauto.
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
  Proof.
  (* нет. доказательство почему нет см в not_type_preservation*)
  admit. Admitted.

  Type type_preservation.
  Definition type_preservation_type := forall (e : expr) (t t' : Typ),
(t') << (t) ->
(e) :-: (t) ->
forall (st : state Z) (e' : expr),
(st) |- e ~~> (e') -> (e') :-: (t').

  Lemma not_type_preservation : ~ type_preservation_type.
  Proof.
  unfold type_preservation_type.
  unfold not.
  intros.
  specialize (H (Var (Id 1)) Int Bool).
  assert (Bool) << (Int). { constructor. }
  specialize (H H0).
  assert (typeOf (Var (Id 1)) Int). { constructor. }
  specialize (H H1).
  specialize (H nil (Var (Id 1))).
  assert (ss_reachable [] (Var (Id 1)) (Var (Id 1))). { constructor. }
  specialize (H H2).
  inversion H.
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
  (* unfold zbool. *)
  intros.
  inversion HT; subst;
  try (inversion HVal;subst; constructor;reflexivity).
  - inversion HVal; subst. inversion BOOLA;subst;inversion BOOLB;subst;eauto.
  - inversion HVal; subst. inversion BOOLA;subst;inversion BOOLB;subst;eauto.
  Qed.

End StaticSemantics.

Module Renaming.
  
  Definition renaming := { f : id -> id | Bijective f }.
  
  Fixpoint rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.
  (* построить обратный ренейминг *)

(* Lemma renaming_inv_og (r : renaming) : exists (r' : renaming), renamings_inv r' r. *)
  
  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof.
    destruct r.
    destruct b.
    destruct a.
    unshelve eexists.
    exists x0.
    unfold Bijective.
    exists x.
    split.
    assumption.
    assumption.
    unfold renamings_inv.
    simpl.
    assumption.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
  destruct r, b, a.
  unshelve eexists.
  exists x0.
  unfold Bijective.
  exists x.
  split.
  assumption.
  assumption.
  unfold renamings_inv.
  simpl.
  assumption.
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
  generalize dependent e.
  induction e.
  - simpl. reflexivity.
  - simpl. f_equal.
  unfold renamings_inv in Hinv.
  apply Hinv.
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
  unfold renamings_inv in Hinv.
  induction st.
  - simpl. reflexivity.
  - destruct r , r'.

  destruct a.
  simpl.
  destruct b , b0.
  destruct a , a0.
  f_equal.
  f_equal.
  auto.
  apply IHst.
Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
  unfold Injective.
  intros.
  destruct BH as [ff a2].
  destruct a2.
  assert (h3 : ff (f x) = ff (f y) ).
  { rewrite H. reflexivity. }
  rewrite H0 in h3.
  rewrite H0 in h3.
  assumption.
  Qed.

Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. 
  constructor.
  Qed.

Lemma get_e1 {b} {e1} {e2} {z} {st} (H : [|Bop b e1 e2|] st => (z)) : exists z' : Z , ([| e1 |] st => (z')).
Proof.
  inversion H; subst; eauto.
Qed.

Lemma get_e2 {b} {e1} {e2} {z} {st} (H : [|Bop b e1 e2|] st => (z)) : exists z' : Z , ([| e2 |] st => (z')).
Proof.
  inversion H; subst; eauto.
Qed.

Lemma vars_case (st : state Z)
(r : renaming)
(i : id)
(z : Z)
: st_eval Z st i = st_eval Z (rename_state r st) (rename_id r i).
Proof.
  generalize dependent st.
  induction st.
  * unfold rename_state.
  constructor.
  *
  destruct r , b , a0 , a. 
  unfold rename_state.
  simpl.
  destruct (id_eq_dec i0 i) eqn:E.
  ** subst. simpl. simpl in IHst.
  destruct (id_eq_dec (x i) (x i)). reflexivity.
  contradiction.
  ** simpl.
  destruct (id_eq_dec (x i0) (x i)).
  ++ destruct n. 
  assert (inj : x0 (x i0) = x0 (x i)). { rewrite e1. reflexivity. }
  rewrite e in inj.
  rewrite e in inj.
  assumption.
  ++
  apply IHst.
Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
  generalize dependent z.
  generalize dependent e.
  induction e.
  -
  split; intros.
  + inversion H; subst.
  constructor.
  + destruct r , b, a.
   unfold rename_state in H.
   simpl in H. inversion H; subst. constructor.
  -
  split;
  intros;
  inversion H; subst;
  constructor;
  apply st_eqiv;
  apply st_eqiv in VAR;
  rewrite <- VAR;
  clear H;
  clear VAR.
  symmetry.
  (* two same goals *)
 
+  
  apply vars_case. apply z.
+ apply vars_case. apply z.

  - 
  split; intros;
  assert (spliter : rename_expr r (Bop b e1 e2) = (Bop b (rename_expr r e1) (rename_expr r e2)));
  eauto.

  
  +
  pose (get_e1 H) as ee1.
  pose (get_e2 H) as ee2.
  inversion ee1; subst.
  inversion ee2; subst.
  apply IHe1 in H0.
  apply IHe2 in H1.
  rewrite spliter.
  inversion H; subst;
  try (
  econstructor;
  try rewrite <- IHe1; 
  try rewrite <- IHe2; 
  eauto; eauto).
  +
  rewrite spliter in H.
  inversion H;subst;
  econstructor;
  try rewrite IHe1; 
  try rewrite IHe2; 
  eauto; eauto.
  Qed.
    
End Renaming.
