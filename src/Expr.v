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

Require Import Coq.Program.Equality.

Module SmokeTest.

  Lemma zero_always x (s : state Z) : [| Var x [*] Nat 0 |] s => Z.zero.
  Proof. admit. Admitted.
  
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. constructor. Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. inversion HH. subst. inversion VALB. subst.
  assert (Az: (za * 2)%Z = (za + za)%Z). { lia. }
  rewrite Az. constructor; auto.
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
Proof. generalize dependent z. induction HSub; intros.
  + exists z. assumption.
  + inversion HV; subst; apply (IHHSub za); assumption.
  + inversion HV; subst; apply (IHHSub zb); assumption.
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
Proof. generalize dependent z. induction e; intros; inversion ID; subst.
  + inversion RED; subst. exists z. assumption.
  + inversion RED; subst.
    all: destruct H3; 
    [apply (IHe1 H za); assumption | apply (IHe2 H zb); assumption].
Qed.


(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. induction e; intros; inversion ID; subst; unfold not; intros.
  + inversion H; subst. specialize (UNDEF z).  contradiction.
  + inversion H; subst.
   all: destruct H3; [apply (IHe1 H0 za); assumption | apply (IHe2 H0 zb); assumption].
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. generalize dependent z1. generalize dependent z2. induction e; intros.
  + inversion E1. inversion E2. subst. reflexivity.
  + inversion E1. inversion E2. subst. apply (state_deterministic Z s i); assumption.
  + inversion E1; inversion E2; subst; try inversion H5.
  all: specialize (IHe1 za VALA za0 VALA0); specialize (IHe2 zb VALB zb0 VALB0); subst; try reflexivity; try contradiction.
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
  + dependent destruction EV. constructor.
  + dependent destruction EV. apply FV in VAR. constructor. assumption. apply v_Var.
  + dependent destruction EV. 
  all: try constructor; auto; auto.
  all: apply IHe1 in EV1; apply IHe2 in EV2; eauto; intros; auto; intros; auto.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. unfold "~~". intros. split; auto. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. unfold "~~" in EQ. unfold "~~". symmetry. auto. Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. unfold "~~" in EQ1. unfold "~~" in EQ2. unfold "~~". 
split; intros.
  + apply EQ2. apply EQ1. assumption.
  + apply EQ1. apply EQ2. assumption.
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
Proof. split; intros.
  + split; intros; generalize dependent n.
    all: induction C; intros;
      [apply H in H0; assumption |
      inversion H0; subst; apply IHC in VALA; auto; econstructor; eassumption |
      inversion H0; subst; apply IHC in VALB; auto; econstructor; eassumption ].
  + split; intros; intros; apply (H Hole); simpl; assumption.
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
  Proof. induction HE; eauto. Qed.

  #[export] Hint Resolve ss_eval_reachable : core.

  Lemma ss_reachable_eval s e z (HR: s |- e ~~> (Nat z)) : s |- e -->> (Nat z).
  Proof. remember (Nat z). induction HR; subst; eauto. Qed.

  #[export] Hint Resolve ss_reachable_eval : core.

  Lemma ss_eval_assoc s e e' e''
                     (H1: s |- e  -->> e')
                     (H2: s |- e' -->  e'') :
    s |- e -->> e''.
  Proof. induction H1; eauto. inversion H2. Qed.
  
  Lemma ss_reachable_trans s e e' e''
                          (H1: s |- e  ~~> e')
                          (H2: s |- e' ~~> e'') :
    s |- e ~~> e''.
  Proof. induction H1; eauto. Qed.

  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').   

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof. intro. intro. inversion HV. subst. destruct H. inversion H. Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. intro. assert (NV: normal_form (Nat 1 [/] Nat 0)).
    + unfold normal_form. intro. intro. destruct H0. inversion H0; subst.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL; subst. inversion VALB; subst. contradiction.
    + specialize (H (Nat 1 [/] Nat 0)). apply H in NV. inversion NV.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. intro. specialize (H (Var (Id 0) [+] Var (Id 1)) (Nat 0 [+] Var (Id 1)) (Var (Id 0) [+] Nat 0) [(Id 0, 0%Z); (Id 1, 0%Z)]). 
    assert (Nat 0 [+] Var (Id 1) <> Var (Id 0) [+] Nat 0).
    { injection; intros. inversion H1. }
    apply H0. apply H.
      + apply ss_Left. apply ss_Var. apply st_binds_hd.
      + apply ss_Right. apply ss_Var. apply st_binds_tl.
        - intro. inversion H1.
        - apply st_binds_hd.
  Qed. 
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. inversion H2; subst; inversion H1; subst.
  + assert (H : z0 = z).
   { apply (state_deterministic Z s i); assumption. }
   subst. reflexivity.
  + inversion LEFT.
  + inversion RIGHT.
  + assert (H: z0 = z).
  { apply (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z0 z); assumption. }
  subst. reflexivity. Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. induction Heval.
    + constructor.
    + assumption. Qed.

  Lemma ss_step_reachable (st : state Z) (e e' : expr) (H : st |- e --> e') : st |- e ~~> e'.
  Proof. eauto. Qed.

  Lemma ss_subst s C e e' (HR: s |- e ~~> e') : s |- (C <~ e) ~~> (C <~ e').
  Proof. induction C; eauto; simpl;
    induction IHC; eauto; eauto.
  Qed.
    
  Lemma ss_subst_binop s e1 e2 e1' e2' op (HR1: s |- e1 ~~> e1') (HR2: s |- e2 ~~> e2') :
    s |- (Bop op e1 e2) ~~> (Bop op e1' e2').
  Proof. apply (ss_subst s (BopL op Hole e2)) in HR1. simpl in HR1.
    apply (ss_subst s (BopR op e1' Hole)) in HR2. simpl in HR2.
    eapply ss_reachable_trans; eauto. Qed.

  Lemma ss_bop_reachable s e1 e2 op za zb z
    (H : [|Bop op e1 e2|] s => (z))
    (VALA : [|e1|] s => (za))
    (VALB : [|e2|] s => (zb)) :
    s |- (Bop op (Nat za) (Nat zb)) ~~> (Nat z).
  Proof. inversion H; subst; 
    apply (eval_deterministic _ _ _ _ VALA) in VALA0;
    apply (eval_deterministic _ _ _ _ VALB) in VALB0; 
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
  Proof. apply ss_eval_reachable in IHe1. apply ss_eval_reachable in IHe2.
    apply ss_reachable_eval.
    eapply ss_reachable_trans. eapply ss_subst_binop; eassumption.
    apply ss_bop_reachable with (e1:=e1) (e2:=e2); assumption.
  Qed.

  #[export] Hint Resolve ss_eval_binop : core.

Lemma ss_eval_destruct (e1 e2 : expr)
                     (s : state Z)
                     (z : Z)
                     (op : bop)
                     (H : s |- Bop op e1 e2 -->> (Nat z))
                : exists za zb, s |- e1 -->> (Nat za) /\ s |- e2 -->> (Nat zb) /\ s |- Bop op (Nat za) (Nat zb) -->> (Nat z).
  Proof.
    remember (Bop op e1 e2). remember (Nat z). generalize dependent e1. generalize dependent e2.
    induction H; intros; subst. inversion Heqe. 
    inversion HStep; subst.
    * destruct IHss_eval with (e2:= e2) (e1:= l') as [za [zb [HL [HR HE]]]]; eauto.
      exists za. exists zb. eauto.
    * destruct IHss_eval with (e2:= r') (e1:= e1) as [za [zb [HL [HR HE]]]]; eauto.
      exists za. exists zb. eauto.
    * inversion H; subst; try inversion HStep0.
      exists zl. exists zr. eauto.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. split; intros; generalize dependent z.
    + induction e; intros;
      [ inversion H; subst; constructor
       | inversion H; subst; apply (se_Step s (Var i) (Nat z)); constructor; assumption
       | inversion H; subst; specialize (IHe1 za VALA); specialize (IHe2 zb VALB); eapply ss_eval_binop; eauto ].
    + induction e; intros.
      - inversion H; subst; eauto. inversion HStep.
      - inversion H; subst; eauto. inversion HStep; 
      subst. constructor. inversion Heval; subst; eauto. inversion HStep0.
      - destruct (ss_eval_destruct _ _ _ _ _ H) as [za [zb [HL [HR HE]]]].
      inversion HE; subst. inversion HStep; subst.
        * inversion LEFT.
        * inversion RIGHT.
        * inversion Heval; subst; try inversion HStep0.
          specialize (IHe1 za HL). specialize (IHe2 zb HR).
          inversion EVAL; inversion VALA; inversion VALB; subst; eauto.
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

  #[export] Hint Constructors subtype : core.

  Lemma subtype_trans t1 t2 t3 (H1: t1 << t2) (H2: t2 << t3) : t1 << t3.
  Proof. destruct t1, t2, t3; auto.

  Lemma subtype_antisymm t1 t2 (H1: t1 << t2) (H2: t2 << t1) : t1 = t2.
  Proof. destruct t1, t2; auto. 
    - inversion H1.
    - inversion H2.
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
  | type_Sup : forall e t t' (H : e :-: t) (HS : t << t'), e :-: t'
  where "e :-: t" := (typeOf e t).

  #[export] Hint Constructors typeOf : core.

  Lemma natBoolOrNot : forall z, zbool z \/ ~zbool z.
  Proof. intros. destruct (Z.eq_dec z 0).
    + left. unfold zbool. auto.
    + destruct (Z.eq_dec z 1). 
      - left. unfold zbool. auto.
      - right. unfold zbool. intro.
      destruct H. auto. auto.
  Qed.

  Lemma type_preserve_small_step st e e' t (HR: (st) |- e --> e') (HT : e :-: t) : (e') :-: t.
  Proof.
    generalize dependent t.
    induction HR; intros.
    + admit.
    + inversion HT; subst. 
    1-5: specialize (IHHR Int H4); auto.
    1-6: specialize (IHHR Int H4); auto. 
    1-2: specialize (IHHR Bool H4); auto.
      

  Lemma type_preservation st e t (HT: e :-: t) : forall e' (HR: st |- e ~~> e'), exists t', e' :-: t' /\ t' << t.
  Proof.
    intros. generalize dependent t.
    induction HR; intros; auto.
    + exists t. split. auto. auto.
    + assert (A: exists t', e' :-: t').
      { inversion HStep; subst.
      + inversion HR; subst; try inversion HStep0. 
     inversion HT; subst. destruct (natBoolOrNot z). 
     - exists Bool. inversion H; subst; econstructor. 
     - exists Int.  econstructor. eassumption.
     - admit. Admitted. Admitted. Qed.

  Lemma type_bool e (HT : e :-: Bool) :
    forall st z (HVal: [| e |] st => z), zbool z.
  Proof. admit. Admitted.

End StaticSemantics.

Module Renaming.
  
  Definition renaming : Set := { f : id -> id | Bijective f }.
  
  Definition rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.
  
  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof. destruct r, b, a. exists (exist _ x0 (ex_intro (fun g => (forall y : id, g (x0 y) = y) /\ (forall x1 : id, x0 (g x1) = x1)) x (conj e0 e))). unfold renamings_inv. simpl. assumption. Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. destruct r, b, a.  exists (exist _ x0 (ex_intro (fun g => (forall y : id, g (x0 y) = y) /\ (forall x1 : id, x0 (g x1) = x1)) x (conj e0 e))). unfold renamings_inv. simpl. assumption. Qed.

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
  Proof. dependent induction e; simpl.
    + reflexivity.
    + rewrite Hinv. reflexivity.
    + rewrite IHe1, IHe2. reflexivity.
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
    + reflexivity.
    + simpl. destruct r', a, r. simpl. rewrite IHst. rewrite Hinv. reflexivity.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. destruct BH, H. unfold Injective. intros x0. intros x1. intros H1.
   apply f_equal with (f := x) in H1. rewrite (H x0) in H1. rewrite (H x1) in H1. assumption. Qed.
  
  Lemma state_renaming_invariance (i : id) (s : state Z) (z : Z) (r : renaming)
    : s / i => z <-> (rename_state r s) / rename_id r i => z.
  Proof. split; intros.
    + dependent induction H; simpl; destruct r; simpl; constructor.
      - unfold "<>". intros. apply H. eapply bijective_injective; eassumption.
      - apply IHst_binds.
    + dependent induction H; simpl; destruct r; simpl; dependent destruction s; inversion x.
      - simpl in x. dependent destruction p. dependent destruction x. clear H0. 
        apply bijective_injective in b. apply b in x. rewrite x. constructor.
      - simpl in H2, H, H0, IHst_binds. dependent destruction p. 
      dependent destruction H2. constructor.
        * intro. apply H. rewrite H1. reflexivity.
        * eapply IHst_binds; reflexivity.
  Qed.   

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. split; intros.
    + dependent induction H; 
      try by econstructor; try eauto.
      econstructor. apply state_renaming_invariance. assumption.
    + dependent induction H; 
      dependent destruction e; dependent destruction x;
      try by econstructor; try eauto.
      econstructor. eapply state_renaming_invariance. eassumption.    
Qed.    
    
End Renaming.
