Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.
Require Import Coq.Program.Equality.

Require Import List.
Import ListNotations.


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
  Proof. 
    apply bs_Nat.
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. 
    inversion HH. inversion VALB. subst.
    assert ((za * 2)%Z = (za + za)%Z). lia.
    rewrite H. apply bs_Add. exact VALA. exact VALA.
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
  induction e; intros; inversion HSub; subst; eauto.
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
  induction e; intros.
  - inversion ID.
  - inversion ID. inversion RED. exists z. subst id. auto. 
  - inversion_clear RED; inversion_clear ID; inversion_clear H; eauto. 
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. 
  intros.
  pose proof (defined_expression e s z id) as H1.
  intro H.
  pose proof (H1 H ID) as H2.
  inversion H2.
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
  - intros. inversion E1. inversion E2.
    rewrite <- H2. auto. 
  - intros. inversion E1. inversion E2.
    eapply state_deterministic.
    + apply VAR.
    + apply VAR0.
  - destruct b;
    inversion_clear E1; inversion_clear E2; 
    pose proof (IHe1 za VALA za0 VALA0) as H1;
    pose proof (IHe2 zb VALB zb0 VALB0) as H2;
    subst; auto.
    all: (subst; contradict OP; auto).
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
  - inversion EV. constructor. 
  - inversion EV. constructor. apply FV. constructor. auto. 
  - inversion_clear EV.
    all: (econstructor; eauto; [eapply IHe1 | eapply IHe2 ]; eauto; intros; eapply FV; econstructor; eauto).
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. 
  unfold equivalent.
  intuition.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. 
  unfold equivalent. intros.
  apply iff_sym. auto.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. 
  unfold equivalent.
  unfold equivalent in EQ1.
  unfold equivalent in EQ2.
  intros. apply (iff_trans (EQ1 n s) (EQ2 n s)).
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
  - intro. unfold contextual_equivalent. intro. 
    induction C. unfold plug. auto.
    all: unfold plug; fold plug; unfold equivalent in *; intros;
        split; intros; inversion H0;
        try apply IHC in VALA; try apply IHC in VALB; econstructor; eauto.
  - intro.
    unfold contextual_equivalent in H.
    specialize (H Hole). simpl in H.
    auto.
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
    inversion HV. subst. intro. intro. inversion H. inversion H0.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. 
    intro. remember (Nat 0 [/] Nat 0).
    assert (normal_form e). intro. intro. destruct H0. subst. inversion H0.
    inversion LEFT. inversion RIGHT.
    inversion EVAL. inversion VALB. subst. contradiction.
    remember (H e H0). inversion i. subst. inversion H1.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. 
    unfold not. intros.
    remember ((Nat Z.one) [*] (Nat Z.zero)) as e1.
    remember ((Nat Z.one) [+] (Nat Z.one)) as e2.
    remember (e1 [+] e2) as e.
    remember ((Nat Z.zero) [+] e2) as e'.
    remember ((e1 [+] (Nat Z.two))) as e''.
    remember (List.nil (A:=(id * Z))) as empty.
    specialize (H e e' e'' empty).
    assert ((e' = e'') -> False).
    - intro.
      subst.
      inversion H0.
    - apply H0. apply H.
      subst.
      constructor. constructor.
      replace (Z.zero)%Z with (Z.one * Z.zero)%Z.
      auto. auto.
      subst.
      constructor. constructor.
      replace (Z.two)%Z with (Z.one + Z.one)%Z.
      auto. auto.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. 
    inversion H1.
    - subst.
      inversion H2.
      assert (z0 = z).
      eapply state_deterministic. eauto. eauto.
      rewrite H4. reflexivity.
    - subst. inversion H2.
      + inversion LEFT.
      + inversion RIGHT. 
      + assert (z = z0).
        eapply eval_deterministic. eauto. eauto.
        rewrite H6. reflexivity.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. 
    induction Heval. apply isv_Intro. exact IHHeval.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
   Proof. admit. Admitted.
  
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
    destruct r, b, a. exists (exist Bijective x0 (ex_intro _ x (conj e0 e))).
    intro. simpl. apply e.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. 
    destruct r, b, a. exists (exist Bijective x0 (ex_intro _ x (conj e0 e))).
    intro. simpl. apply e0.
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
    destruct r, r'. induction e; simpl.
    - reflexivity.
    - assert (x (x0 i) = i). apply (Hinv i). rewrite H. reflexivity.
    - rewrite IHe1. rewrite IHe2. reflexivity.
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
    destruct r, r'. induction st.
    - reflexivity.
    - destruct a. simpl. assert (x (x0 i) = i). apply (Hinv i). rewrite H. rewrite IHst. reflexivity.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
     intro. intros. 
     destruct BH. destruct H0. 
     rewrite <- (H0 x). rewrite <- (H0 y). rewrite H. reflexivity. 
  Qed.

  Lemma eval_renaming_invariance_helper (e : expr) (st : state Z) (z : Z) (r : renaming) :
    [| e |] st => z -> [| rename_expr r e |] (rename_state r st) => z.
  Proof. 
    intro. generalize st z r H. clear H r z st. induction e; intros; inversion H; clear H.
    - apply bs_Nat.
    - apply bs_Var. subst. induction VAR; destruct r.
      + apply st_binds_hd.
      + apply st_binds_tl; simpl.
        intro. remember (bijective_injective x0 b). assert (id = id'). apply i. 
        * exact H0. 
        * contradiction.
        * exact IHVAR.
    - apply bs_Add. apply IHe1. exact VALA. apply IHe2. exact VALB.
    - apply bs_Sub. apply IHe1. exact VALA. apply IHe2. exact VALB.
    - apply bs_Mul. apply IHe1. exact VALA. apply IHe2. exact VALB.
    - apply bs_Div. apply IHe1. exact VALA. apply IHe2. exact VALB. exact NZERO.
    - apply bs_Mod. apply IHe1. exact VALA. apply IHe2. exact VALB. exact NZERO.
    - apply bs_Le_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Le_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Lt_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Lt_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Ge_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Ge_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Gt_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Gt_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Eq_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Eq_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Ne_T with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_Ne_F with za zb. apply IHe1. exact VALA. apply IHe2. exact VALB. exact OP.
    - apply bs_And. apply IHe1. exact VALA. apply IHe2. exact VALB. exact BOOLA. exact BOOLB.
    - apply bs_Or. apply IHe1. exact VALA. apply IHe2. exact VALB. exact BOOLA. exact BOOLB.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. 
    split; intro.
    - apply eval_renaming_invariance_helper. exact H.
    - destruct (renaming_inv r).
      assert ([|rename_expr x (rename_expr r e)|] (rename_state x (rename_state r st)) => z). 
      + apply eval_renaming_invariance_helper. exact H.
      + assert (rename_expr x (rename_expr r e) = e).
        * apply re_rename_expr. exact H0.
        * assert (rename_state x (rename_state r st) = st).
          apply re_rename_state. 
          ** exact H0.
          ** rewrite -> H2 in H1. rewrite -> H3 in H1. exact H1.
  Qed.
    
End Renaming.
