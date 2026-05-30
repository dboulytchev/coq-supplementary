Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
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

  Lemma zero_always x (s : state Z) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof. Admitted.
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. apply bs_Nat. Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH; subst.
    inversion VALB; subst.
    replace (za * 2)%Z with (za + za)%Z by lia.
    apply bs_Add; assumption.
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
  generalize dependent z.
  induction HSub as [e | e e1 e2 op HS IH | e e1 e2 op HS IH]; intros z HV.
  - exists z. assumption.
  - inversion HV; subst; eapply IH; eassumption.
  - inversion HV; subst; eapply IH; eassumption.
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
  induction e as [n | i | op e1 IH1 e2 IH2]; intros z RED.
  - inversion ID.
  - inversion ID; subst. inversion RED; subst. exists z. assumption.
  - inversion ID; subst.
    match goal with
    | [HO : _ \/ _ |- _] => destruct HO as [HE1 | HE2]
    end.
    + inversion RED; subst; eapply IH1; eassumption.
    + inversion RED; subst; eapply IH2; eassumption.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros z RED.
  destruct (defined_expression e s z id RED ID) as [z' Hb].
  apply (UNDEF z'). assumption.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z2.
  induction E1; intros z2 E2; inversion E2; subst;
    try reflexivity;
    try (eapply state_deterministic; eauto; fail);
    try (
      match goal with
      | [IH1 : forall z, [| ?a |] ?s => z -> _ = z,
         IH2 : forall z, [| ?b |] ?s => z -> _ = z,
         HA  : [| ?a |] ?s => _,
         HB  : [| ?b |] ?s => _ |- _] =>
          pose proof (IH1 _ HA) as HEqa;
          pose proof (IH2 _ HB) as HEqb;
          subst
      end;
      unfold Z.eq in *;
      try reflexivity;
      try (exfalso; lia);
      try lia;
      try (unfold zbool in *; lia)
    ).
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
  induction e as [n | i | op e1 IH1 e2 IH2]; intros z EV.
  - inversion EV; subst. apply bs_Nat.
  - inversion EV; subst.
    apply bs_Var. apply (FV i (v_Var i)). assumption.
  - assert (FV1 : forall id, id ? e1 -> equivalent_states s1 s2 id)
      by (intros id0 Hid; apply FV; apply v_Bop; left; assumption).
    assert (FV2 : forall id, id ? e2 -> equivalent_states s1 s2 id)
      by (intros id0 Hid; apply FV; apply v_Bop; right; assumption).
    inversion EV; subst;
      first
        [ apply bs_Add
        | apply bs_Sub
        | apply bs_Mul
        | apply bs_Div
        | apply bs_Mod
        | apply (bs_Le_T s2 e1 e2 za zb)
        | apply (bs_Le_F s2 e1 e2 za zb)
        | apply (bs_Lt_T s2 e1 e2 za zb)
        | apply (bs_Lt_F s2 e1 e2 za zb)
        | apply (bs_Ge_T s2 e1 e2 za zb)
        | apply (bs_Ge_F s2 e1 e2 za zb)
        | apply (bs_Gt_T s2 e1 e2 za zb)
        | apply (bs_Gt_F s2 e1 e2 za zb)
        | apply (bs_Eq_T s2 e1 e2 za zb)
        | apply (bs_Eq_F s2 e1 e2 za zb)
        | apply (bs_Ne_T s2 e1 e2 za zb)
        | apply (bs_Ne_F s2 e1 e2 za zb)
        | apply bs_And
        | apply bs_Or ];
      try (apply IH1; auto);
      try (apply IH2; auto);
      try assumption.
  Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  unfold equivalent. intros n s. split; intro H; assumption.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent in *. intros n s.
  specialize (EQ n s). split; apply EQ.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in *. intros n s.
  specialize (EQ1 n s). specialize (EQ2 n s).
  split; intro H; [apply EQ2, EQ1 | apply EQ1, EQ2]; assumption.
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
  split.
  - intro EQ. unfold contextual_equivalent.
    intro C. induction C; simpl.
    + assumption.
    + (* BopL b C e0 *)
      unfold equivalent in *. intros n s. split; intro HV;
        inversion HV; subst;
        first
          [ apply bs_Add
          | apply bs_Sub
          | apply bs_Mul
          | apply bs_Div
          | apply bs_Mod
          | apply (bs_Le_T s _ _ za zb)
          | apply (bs_Le_F s _ _ za zb)
          | apply (bs_Lt_T s _ _ za zb)
          | apply (bs_Lt_F s _ _ za zb)
          | apply (bs_Ge_T s _ _ za zb)
          | apply (bs_Ge_F s _ _ za zb)
          | apply (bs_Gt_T s _ _ za zb)
          | apply (bs_Gt_F s _ _ za zb)
          | apply (bs_Eq_T s _ _ za zb)
          | apply (bs_Eq_F s _ _ za zb)
          | apply (bs_Ne_T s _ _ za zb)
          | apply (bs_Ne_F s _ _ za zb)
          | apply bs_And
          | apply bs_Or ];
        try (apply IHC; eassumption);
        try assumption.
    + (* BopR b e0 C *)
      unfold equivalent in *. intros n s. split; intro HV;
        inversion HV; subst;
        first
          [ apply bs_Add
          | apply bs_Sub
          | apply bs_Mul
          | apply bs_Div
          | apply bs_Mod
          | apply (bs_Le_T s _ _ za zb)
          | apply (bs_Le_F s _ _ za zb)
          | apply (bs_Lt_T s _ _ za zb)
          | apply (bs_Lt_F s _ _ za zb)
          | apply (bs_Ge_T s _ _ za zb)
          | apply (bs_Ge_F s _ _ za zb)
          | apply (bs_Gt_T s _ _ za zb)
          | apply (bs_Gt_F s _ _ za zb)
          | apply (bs_Eq_T s _ _ za zb)
          | apply (bs_Eq_F s _ _ za zb)
          | apply (bs_Ne_T s _ _ za zb)
          | apply (bs_Ne_F s _ _ za zb)
          | apply bs_And
          | apply bs_Or ];
        try (apply IHC; eassumption);
        try assumption.
  - intro CEQ. specialize (CEQ Hole). simpl in CEQ. assumption.
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
    - eapply reach_step; eauto.
  Qed.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof.
    remember (Nat z) as v eqn:Hv. revert Hv.
    induction HR; intro Hv.
    - subst. apply se_Stop.
    - eapply se_Step; eauto.
  Qed.

  #[export] Hint Resolve ss_eval_reachable : core.
  #[export] Hint Resolve ss_reachable_eval : core.
  
  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof.
    induction H1.
    - (* e' = Nat z, but Nat z --> e'' is impossible *)
      inversion H2.
    - eapply se_Step; eauto.
  Qed.

  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof.
    induction H1.
    - assumption.
    - eapply reach_step; eauto.
  Qed.
          
  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    inversion HV; subst.
    unfold normal_form. intros s [e' Hstep].
    inversion Hstep.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    intro H.
    (* Pick e = Nat 1 [/] Nat 0: it has no step (b=0 blocks ss_Bop, both subexprs are values) *)
    pose (e := Nat 1 [/] Nat 0).
    assert (NF : normal_form e).
    { unfold normal_form, e. intros s [e' Hstep]. inversion Hstep; subst.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL; subst.
        inversion VALB; subst.
        apply NZERO. reflexivity. }
    specialize (H e NF). inversion H.
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
    remember (Nat z) as N eqn:HN.
    revert e' H2.
    induction H1; intros e' H2.
    - (* ss_Var: e = Var i; HN: Nat z0 = Nat z *)
      injection HN as HN'. subst z0.
      inversion H2; subst.
      f_equal. eapply state_deterministic; eauto.
    - discriminate.
    - discriminate.
    - (* ss_Bop applied *)
      inversion H2; subst.
      + inversion LEFT.
      + inversion RIGHT.
      + injection HN as HN'. subst z0.
        f_equal. eapply eval_deterministic; eassumption.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - constructor.
    - assumption.
  Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof.
    induction C; simpl.
    - assumption.
    - induction IHC.
      + apply reach_base.
      + eapply reach_step; [apply ss_Left; eassumption | assumption].
    - induction IHC.
      + apply reach_base.
      + eapply reach_step; [apply ss_Right; eassumption | assumption].
  Qed.

  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof.
    apply ss_reachable_trans with (Bop op e1' e2).
    - exact (ss_subst s (BopL op Hole e2) e1 e1' HR1).
    - exact (ss_subst s (BopR op e1' Hole) e2 e2' HR2).
  Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof.
    apply reach_step with (e' := Nat z).
    2: apply reach_base.
    apply ss_Bop.
    inversion H; subst;
      assert (Hza : za0 = za) by (eapply eval_deterministic; eauto);
      assert (Hzb : zb0 = zb) by (eapply eval_deterministic; eauto);
      subst za0; subst zb0;
      try (econstructor; try apply bs_Nat; try assumption).
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
    apply ss_reachable_trans with (Bop op (Nat za) (Nat zb)).
    - apply ss_subst_binop; apply ss_eval_reachable; assumption.
    - eapply ss_bop_reachable; eassumption.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. admit. Admitted.
  
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
    inversion H1; subst; inversion H2; subst; try assumption; try constructor.
  Qed.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof.
    inversion H1; subst; inversion H2; subst; reflexivity.
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
  Proof. Admitted.

  Lemma type_preservation_contra :
    not (forall e t t' st e', t' << t -> e :-: t -> st |- e ~~> e' -> e' :-: t').
  Proof.
    intro H.
    set (e := Nat 2).
    set (t := Int).
    set (t' := Bool).
    assert (t' << t) as Sub by constructor.
    assert (e :-: t) as Typ.
    { unfold e, t. apply type_N. unfold zbool. intros [H1|H1]; discriminate. }
    assert ([] |- e ~~> e) as Eval by constructor.
    specialize (H e t t' [] e Sub Typ Eval).
    unfold e in H.
    inversion H.
  Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof.
    induction e; intros; inversion HT; subst;
      try (inversion HVal; subst;
            match goal with
            | _ => right; tauto
            | _ => constructor; tauto
            end);
      try (inversion HVal; subst;
            inversion BOOLA; inversion BOOLB; subst;
            constructor; tauto || (right; tauto)).
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
    destruct r as [f Hbij].
    destruct Hbij as [g [Hgf Hfg]].
    assert (Hbij_g : Bijective g) by (exists f; split; [apply Hfg | apply Hgf]).
    exists (exist _ g Hbij_g).
    unfold renamings_inv. simpl. intro x. apply Hgf.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r as [f Hbij].
    destruct Hbij as [g [Hgf Hfg]].
    assert (Hbij_g : Bijective g) by (exists f; split; [apply Hfg | apply Hgf]).
    exists (exist _ g Hbij_g).
    unfold renamings_inv. simpl. intro x. apply Hfg.
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
    induction e as [n | i | op e1 IH1 e2 IH2]; simpl.
    - reflexivity.
    - rewrite Hinv. reflexivity.
    - rewrite IH1. rewrite IH2. reflexivity.
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
    - simpl. destruct r. destruct r'. reflexivity.
    - destruct a as [i v]. simpl.
      pose proof (Hinv i) as Hi.
      destruct r' as [f' Hb']. destruct r as [f Hb]. simpl in *.
      rewrite Hi.
      f_equal.
      apply IHst.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    destruct BH as [g [Hgf _]].
    intros x y Hfxy.
    rewrite <- (Hgf x), <- (Hgf y). f_equal. assumption.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. Admitted.
    
End Renaming.
