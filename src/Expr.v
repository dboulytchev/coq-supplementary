Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

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
  Proof. apply bs_Nat. Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. inversion HH. inversion VALB. subst. 
    assert ((za * 2)%Z = (za + za)%Z).
      lia.
    rewrite H. constructor. auto. auto.
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
Proof. generalize dependent z. induction e.
  + intros. inversion HV. inversion HSub. subst. exists z0. auto.
  + intros. inversion HV. inversion HSub. subst. exists z. auto.
  + inversion HSub.
    * intros. exists z. auto.
    * intros. subst; inversion HV; subst; eapply IHe1; eauto.
    * intros. subst; inversion HV; subst; eapply IHe2; eauto.
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
Proof. generalize dependent z. induction e.
  - inversion ID.
  - intros. exists z. inversion RED. inversion ID. subst. auto.
  - intros. inversion ID. destruct H3.
      * eapply (strictness (Bop b e1 e2) e1) in RED. destruct RED.
        apply IHe1 with x. auto. auto. apply subexpr_left. apply subexpr_refl.
      * eapply (strictness (Bop b e1 e2) e2) in RED. destruct RED.
        apply IHe2 with x. auto. auto. apply subexpr_right. apply subexpr_refl.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. intros. intro.
       apply (defined_expression e s z id) in H.
      destruct H. specialize (UNDEF x). contradiction. auto.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. generalize dependent z1.
      generalize dependent z2.
      induction e.
    + intros. inversion E1. inversion E2. subst. auto.
    + intros. inversion E1. inversion E2. subst. 
      eapply state_deterministic in VAR. eauto. auto.
    + intros. destruct b.
      all: inversion E2; inversion E1.
      all: try apply (IHe1 za0) in VALA.
      all: try apply (IHe2 zb0) in VALB.
      all: subst.
      all: auto.
      all: contradiction.
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
    induction EV.
    constructor.
    constructor. specialize (FV i). apply FV. subst. apply v_Var. auto.
    all: econstructor; auto; auto.
    all: try apply IHEV1.
    all: try apply IHEV2.
    all: intros.
    all: try apply FV.
    all: try apply v_Bop.
    all: auto.
Qed.


Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. intro. intro. reflexivity. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. intro. intro. split.
  + apply EQ.
  + apply EQ.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. intro. intro. split.
  + intro. apply EQ1 in H. apply EQ2 in H. auto.
  + intro. apply EQ2 in H. apply EQ1 in H. auto.
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
Proof. split.
  * intro. intro. intro.
    generalize dependent n.
    induction C.
    intros. auto. 
    intros. auto. 
    destruct b.
    all: econstructor.
    all: intro.
    all: inversion H0.
    all: econstructor.
    all: try apply IHC.
    all: try apply VALA.
    all: try apply VALB.
    all: auto.
  * intro. specialize (H Hole). auto.
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
  Proof. intro. intro. inversion HV. subst. destruct H. inversion H. Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. intro.
    remember (Bop Div (Nat 0) (Nat 0)).
    assert (normal_form e). 
      intro. intro. destruct H0. subst.
      inversion H0.
      inversion LEFT.
      inversion RIGHT.
      inversion EVAL. inversion VALB. subst. contradiction.
    apply H in H0. inversion H0. subst. inversion H1.
  Qed.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. intro. 
    remember (H
    (Bop Mul (Bop Add (Nat 2) (Nat 1)) ((Bop Add (Nat 3) (Nat 4))))
    (Bop Mul ((Nat (2 + 1))) (Bop Add (Nat 3) (Nat 4)))
    (Bop Mul (Bop Add (Nat 2) (Nat 1)) (Nat (3 + 4)))
    []).
    assert (Bop Mul (Nat (2 + 1)) (Bop Add (Nat 3) (Nat 4)) <> (Bop Mul (Bop Add (Nat 2) (Nat 1)) (Nat (3 + 4)))).
    intro. inversion H0.
    apply H0. apply e.
    apply ss_Left.  apply ss_Bop. apply bs_Add. auto. auto.
    apply ss_Right. apply ss_Bop. apply bs_Add. auto. auto.
  Qed.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. inversion H1.
    + subst. inversion H2.
      apply (state_deterministic _ s i z z0) in VAL0.
        - subst. auto.
        - auto.
    + subst. inversion H2.
      - inversion LEFT.
      - inversion RIGHT.
      - apply (eval_deterministic _ s z z0) in EVAL.
        * subst. auto.
        * auto.
  Qed.
  
  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof. induction Heval.
    + apply isv_Intro.
    + apply IHHeval.
  Qed.
  
  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof. admit. Admitted.
  
End SmallStep.

Module Renaming.
  
  Definition renaming := { f : id -> id | Bijective f }.
  
  Definition rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.
  
  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof. destruct r. destruct b.
    assert (Bijective x0).
      exists x. destruct a. auto.
   exists (exist Bijective x0 H).
   intro. destruct a. auto.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. destruct r. destruct b.
    assert (Bijective x0).
      exists x. destruct a. auto.
   exists (exist Bijective x0 H).
   intro. destruct a. auto.
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
  Proof. induction e.
    + auto.
    + simpl. specialize (Hinv i). rewrite Hinv. reflexivity.
    + simpl. rewrite IHe1. rewrite IHe2. reflexivity. 
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
  Proof. induction st.
      * simpl. reflexivity.
      * simpl. destruct a.  destruct r'. destruct r.
        simpl. rewrite IHst. rewrite Hinv. reflexivity.
  Qed.   
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. intros. 
    unfold Injective.  
    destruct BH. intros. 
    destruct H. rewrite <- H. rewrite <- H0. rewrite H. reflexivity.
  Qed.

  Lemma injective_not_equal (x0 : id -> id) (Hinj : Injective x0) (id1 id2 : id) :
    id1 <> id2 -> x0 id1 <> x0 id2.
  Proof. intros. auto. Qed.

  Lemma bijection_eq :
    forall (x0 : id -> id) (x: Bijective x0) (i i0 : id),
    x0 i0 = x0 i -> i = i0.
  Proof.
    intros.
    destruct x. destruct H0. 
    remember (H0 i). rewrite <- e. rewrite <- H. auto.
  Qed.

  Lemma eval_renaming_invariance' (r : renaming) 
                                      (st : state Z) 
                                      (i : id)
                                      (z : Z) :
    ((st) / i => z) <-> ((rename_state r st) / rename_id r i => z).
  Proof. split.
    - intro. destruct r. induction H.
      * constructor.
      * constructor. simpl. apply injective_not_equal.
        apply bijective_injective. auto. auto. auto.
    - generalize dependent z. intro. induction st.
      * intro. inversion H.
      * destruct r, a. intro. inversion H.
        + apply bijection_eq in H4. subst. apply st_binds_hd. auto.
        + constructor.
          -- intro. subst. contradiction.
          -- auto.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. split.
    + generalize dependent z. induction e. 
      * intros. simpl. inversion H. auto. 
      * intros. simpl. inversion H. constructor. rewrite <- eval_renaming_invariance'. auto.
      * induction st.
        simpl. intro. intro. simpl in IHe1. simpl in IHe2.
        all: intros; inversion H.
        all: try econstructor.
        all: (try apply IHe1, VALA).
        all: (try apply IHe2, VALB).
        all: auto.
    + generalize dependent z. induction e.
      - intros. inversion H. auto.
      - intros. inversion H. apply (eval_renaming_invariance' r) in VAR. constructor. auto.
      - intros. simpl. inversion H.
        all: econstructor.
        all: (try apply IHe1, VALA).
        all: (try apply IHe2, VALB).
        all: auto.
  Qed.
    
End Renaming.
