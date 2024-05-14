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

#[export] Hint Constructors eval : core.

Module SmokeTest.

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. constructor. Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. inversion HH. subst. inversion VALB. subst.
    rewrite <- (Zplus_diag_eq_mult_2). constructor; assumption.
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
  induction e; intros; inversion HSub; subst.
  - exists z0. assumption.
  - exists z. assumption.
  - exists z. assumption.
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
      (e : expr) (s : state Z) (z : Z) (idV : id)
      (RED : [| e |] s => z)
      (ID  : idV ? e) :
  exists z', s / idV => z'.
Proof.
  generalize dependent z.
  induction e; intros.
  - inversion ID.
  - inversion ID. subst. inversion RED. subst. exists z. assumption.
  - inversion ID. inversion RED; inversion H3; eauto.
Qed.
(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (idV : id)
      (ID : idV ? e) (UNDEF : forall (z : Z), ~ (s / idV => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  intros. unfold not.
  generalize dependent z.
  induction e; intros.
  - inversion ID.
  - inversion ID. inversion H. subst. apply (UNDEF z) in VAR. assumption.
  - inversion ID. subst. destruct H4.
    + inversion H; subst; apply IHe1 in VALA; assumption.
    + inversion H; subst; apply IHe2 in VALB; assumption.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof. generalize dependent z1. generalize dependent z2. induction e; intros.
  - inversion E1. inversion E2. subst. reflexivity.
  - inversion E1. inversion E2. subst. apply (state_deterministic Z s i z1 z2 VAR VAR0).
  - inversion E1; inversion E2; specialize (IHe1 za VALA za0 VALA0); 
    specialize (IHe2 zb VALB zb0 VALB0); subst;
    try discriminate H5; try reflexivity; contradiction.
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (idx : id) :=
  forall z : Z, s1 / idx => z <-> s2 / idx => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (idx : id) (ID : idx ? e),
          equivalent_states s1 s2 idx)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof. generalize dependent z. induction e; intros.
  - inversion EV. auto.
  - inversion EV. subst.
    assert (forall (i : id), i ? (Var i)).
    + constructor.
    + specialize (FV i). apply FV in H. apply H in VAR. apply (bs_Var s2 i z VAR).
  - assert (forall (idx : id), (idx ? e1) -> equivalent_states s1 s2 idx).
    + intros. apply (FV idx). constructor. left. apply H.
    + assert (forall (idx : id), (idx ? e2) -> equivalent_states s1 s2 idx).
      ++  intros. apply (FV idx). constructor. right. apply H0.
      ++  inversion EV; subst; specialize (IHe1 H za VALA); specialize (IHe2 H0 zb VALB);
      try constructor; try assumption; eauto.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. constructor; intros; assumption. Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. constructor; apply EQ. Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof. constructor; intros; unfold equivalent in EQ1; unfold equivalent in EQ2.
  - apply (EQ1 n s) in H. apply EQ2. assumption.
  - apply (EQ2 n s) in H. apply EQ1. assumption.
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
Proof. split; constructor; intro; generalize dependent n.
  - induction C; intro; specialize (H n s). apply H.
    + simpl. intro. inversion H0; subst; specialize (IHC za VALA); eauto.
    + simpl. intro. inversion H0; subst; specialize (IHC zb VALB); eauto.
  - induction C; intro; specialize (H n s). apply H.
    + simpl. intro. inversion H0; subst; specialize (IHC za VALA); eauto.
    + simpl. intro. inversion H0; subst; specialize (IHC zb VALB); eauto.
  - intro. specialize (H Hole n s). simpl in H. apply H.
  - intro. specialize (H Hole n s). simpl in H. apply H.
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
  Proof. inversion HV. subst. intro. intro. inversion H. inversion H0. Qed.    

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof. intro. specialize (H ((Nat 1) [\/] (Nat 2))). 
    assert (normal_form (Nat 1 [\/] (Nat 2))).
    - intro. intro. inversion H0. inversion H1.
      inversion LEFT. inversion RIGHT.
      inversion EVAL. inversion VALA. inversion VALB. subst. inversion BOOLB.
        discriminate H2. discriminate H2.
    - apply H in H0. inversion H0.
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. intro.
    specialize (H (Var (Id 0) [+] Var (Id 1)) (Nat 42 [+] (Var (Id 1))) (Var (Id 0) [+] Nat 56) [(Id 0, 42%Z); (Id 1, 56%Z)]).
    discriminate H.
    - apply ss_Left. apply ss_Var. apply st_binds_hd.
    - apply ss_Right. apply ss_Var. apply st_binds_tl. discriminate.
      apply st_binds_hd.
  Qed.
    
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof. 
  inversion H1; inversion H2; subst. 
  1-5: inversion H5; subst; remember (state_deterministic Z s i z z1 VAL VAL0); rewrite e; auto.
  - inversion H2; subst. 
    + inversion LEFT0.
    + inversion RIGHT.
  - inversion H2; subst.
    + inversion LEFT.
    + inversion RIGHT0.
  - inversion H2; inversion H1; subst.
    specialize (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z1 z EVAL1 EVAL2). 
    intros. rewrite H. reflexivity.
  Qed. 

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    generalize dependent e. induction e'.
    - intros. apply isv_Intro.
    - intros. induction Heval.
      + apply isv_Intro.
      + assumption.
    - intros. induction Heval.
      + apply isv_Intro.
      + specialize (IHHeval IHe'1 IHe'2). assumption.
  Qed.

  Lemma ss_bs_step_equiv (s   : state Z)
                         (e e': expr)
                         (z : Z)
                         (HST: (s) |- e --> e')
                         (HEX: [|e'|] s => z) : [|e|] s => (z).
  Proof.
    dependent induction e.
    * inversion HST.
    * inversion HST. subst. inversion HEX; subst. auto.
    * dependent induction b;
      inversion HST; subst; inversion HEX; subst; eauto.
  Qed.

  Lemma ss_bop_step_left (e1 e1' e2 : expr)
                  (s : state Z)
                  (b : bop)
                  (z : Z)
                  (LEFT : s |- e1 -->> e1')
                  (HSTEP: s |- Bop b e1' e2 -->> (Nat z)): s |- Bop b e1 e2 -->> (Nat z).
  Proof.
    dependent induction LEFT. assumption.
    econstructor. eapply ss_Left. eassumption.
    apply IHLEFT. assumption.
  Qed.

  Lemma ss_bop_step_right (e1 e2 e2' : expr)
                  (s : state Z)
                  (b : bop)
                  (z : Z)
                  (RIGHT : s |- e2 -->> e2')
                  (STEP: s |- Bop b e1 e2' -->> (Nat z)): s |- Bop b e1 e2 -->> (Nat z).
  Proof.
    dependent induction RIGHT. assumption.
    econstructor. eapply ss_Right. eassumption.
    apply IHRIGHT. assumption.
  Qed.

  Lemma ss_bop_step (e1 e1' e2 e2' : expr)
                 (s : state Z)
                 (b: bop)
                 (z : Z)
                 (LEFT : s |- e1 -->> e1')
                 (RIGHT: s |- e2 -->> e2')
                 (HEBOP: s |- Bop b e1' e2' -->> (Nat z)) : s |- Bop b e1 e2 -->> (Nat z).
  Proof. eapply ss_bop_step_left. apply LEFT.
         eapply ss_bop_step_right. apply RIGHT. apply HEBOP.
  Qed.

  Lemma ss_bop_bs_trans (e1 e2 : expr)
                 (s : state Z)
                 (b: bop)
                 (z z1 z2 : Z)
                 (HEV1 : s |- e1 -->> (Nat z1))
                 (HEV2: s |- e2 -->> (Nat z2))
                 (HEBOP: [|Bop b (Nat z1) (Nat z2)|] s => z) : s |- Bop b e1 e2 -->> (Nat z).
  Proof. 
    eapply ss_bop_step; try by eassumption. econstructor.
    - eapply ss_Bop. eassumption.
    - constructor.
  Qed.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
   Proof. constructor; intro.
    - dependent induction H.
      constructor. 
      econstructor. constructor. eassumption. constructor.
      all: eapply ss_bop_bs_trans; (try by eassumption); econstructor; (try by econstructor); eassumption.
    - dependent induction H.
      + auto.
      + specialize (IHss_eval z). assert (Nat z = Nat z). { reflexivity. } apply IHss_eval in H0.
        specialize (ss_bs_step_equiv s e e' z HStep H0). intro. assumption.
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
  Proof. destruct r as [g bG]. destruct bG as [h H]. destruct H as [HG GH]. 
         exists (exist _ _ (ex_intro _ g (conj GH HG))). unfold renamings_inv. simpl.
         apply HG.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof. destruct r as [g bG]. destruct bG as [h H]. destruct H as [HG GH].
        exists (exist _ _ (ex_intro _ g (conj GH HG))). unfold renamings_inv. simpl.
        apply GH.
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
  Proof. dependent induction e.
    - reflexivity.
    - unfold rename_expr. specialize (Hinv i).
    rewrite Hinv. reflexivity.
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
  Proof. dependent induction st.
    - reflexivity.
    - simpl. destruct a. destruct r as [g bG]. destruct bG as [h H].
      destruct H as [HG GH]. destruct r' as [g' bG']. destruct bG' as [h' H'].
      destruct H' as [HG' GH']. unfold renamings_inv in Hinv. simpl in Hinv. simpl.
      rewrite IHst. 
      + rewrite Hinv. reflexivity.
      + reflexivity.
      + reflexivity.
  Qed.
      
  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof. inversion BH as [g H]. inversion H. unfold Injective. intros.
    specialize (H0 x). inversion H. specialize (H3 y).
   rewrite H2 in H0. rewrite <- H0. rewrite -> H3. reflexivity.
  Qed.

  Lemma state_renaming_invariance (x : id) 
                                  (st : state Z) 
                                  (z : Z) 
                                  (r: renaming) : st / x => z <-> (rename_state r st) / rename_id r x  => z.
  Proof. split; intro;
  (try by inversion H); subst; destruct r as [g bG]; dependent induction H.
    - apply st_binds_hd.
    - apply st_binds_tl.
      + intro. apply H. eapply bijective_injective. simpl in H1.
        * apply bG.
        * apply H1.
      + apply IHst_binds.
    - destruct st.
      + discriminate x.
      + destruct p. dependent destruction x. 
        remember (bijective_injective g bG) as BIG.
        apply (BIG x1 i) in x. rewrite x. apply st_binds_hd.
    - destruct st.
      + discriminate x.
      + destruct p. dependent destruction x. simpl in H. simpl in H0. simpl in IHst_binds.
        apply st_binds_tl.
        * intro. apply H. rewrite H1. reflexivity.
        * apply (IHst_binds x1 st z g bG); reflexivity.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r : renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof. generalize dependent z. induction e.
  - split; intros; inversion H; subst; apply bs_Nat.
  - split; intros.
    + simpl. inversion H. subst. apply bs_Var. apply state_renaming_invariance. assumption.
    + inversion H. subst. apply state_renaming_invariance in VAR. apply bs_Var. assumption.
  - split; intros.
    + inversion H; subst;
      specialize (IHe1 za); specialize (IHe2 zb); simpl; 
      apply IHe1 in VALA; apply IHe2 in VALB; 
      auto; econstructor; try apply VALA; try apply VALB; try apply OP.
    + inversion H; subst;
      specialize (IHe1 za); specialize (IHe2 zb); apply IHe1 in VALA;
      apply IHe2 in VALB; try econstructor; try eassumption.
  Qed.    
    
End Renaming.
