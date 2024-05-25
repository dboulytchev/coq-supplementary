Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

Require Import List.
Import ListNotations.

(* From hahn Require Import HahnBase. *)

Declare Scope expr_scope.
Open Scope expr_scope.

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
Notation "x '[+]'  y" := (Bop Add x y) (at level 40, left associativity) : expr_scope.
Notation "x '[-]'  y" := (Bop Sub x y) (at level 40, left associativity) : expr_scope.
Notation "x '[*]'  y" := (Bop Mul x y) (at level 41, left associativity) : expr_scope.
Notation "x '[/]'  y" := (Bop Div x y) (at level 41, left associativity) : expr_scope.
Notation "x '[%]'  y" := (Bop Mod x y) (at level 41, left associativity) : expr_scope.
Notation "x '[<=]' y" := (Bop Le  x y) (at level 39, no associativity) : expr_scope.
Notation "x '[<]'  y" := (Bop Lt  x y) (at level 39, no associativity) : expr_scope.
Notation "x '[>=]' y" := (Bop Ge  x y) (at level 39, no associativity) : expr_scope.
Notation "x '[>]'  y" := (Bop Gt  x y) (at level 39, no associativity) : expr_scope.
Notation "x '[==]' y" := (Bop Eq  x y) (at level 39, no associativity) : expr_scope.
Notation "x '[/=]' y" := (Bop Ne  x y) (at level 39, no associativity) : expr_scope.
Notation "x '[&]'  y" := (Bop And x y) (at level 38, left associativity) : expr_scope.
Notation "x '[\/]' y" := (Bop Or  x y) (at level 38, left associativity) : expr_scope.

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
  Proof.
    inversion HH. subst e. inversion VALB.
    assert ((za * 2)%Z = (za + za)%Z). { lia. }
    rewrite H. constructor; apply VALA.
  Qed.
End SmokeTest.

(* A relation of one expression being of a subexpression of another *)
Reserved Notation "e1 << e2" (at level 0).

Inductive subexpr : expr -> expr -> Prop :=
  subexpr_refl : forall e : expr, e << e
| subexpr_left : forall e e' e'' : expr, forall op : bop, e << e' -> e << (Bop op e' e'')
| subexpr_right : forall e e' e'' : expr, forall op : bop, e << e'' -> e << (Bop op e' e'')
where "e1 << e2" := (subexpr e1 e2) : expr_scope.

Lemma strictness (e e' : expr) (HSub : e' << e) (st : state Z) (z : Z) (HV : [| e |] st => z) :
  exists z' : Z, [| e' |] st => z'.
Proof.
  generalize dependent z.
  induction e; intros; inversion HSub.
  - exists z0. assumption.
  - exists z. assumption.
  - exists z. assumption.
  - inversion HV; try (apply IHe1 with (z:=za); assumption; assumption).
  - inversion HV; try (apply IHe2 with (z:=zb); assumption; assumption).
  Qed.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop :=
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (a b : expr) (op : bop), id ? a \/ id ? b -> id ? (Bop op a b)
where "x ? e" := (V e x) : expr_scope.

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
  induction e; intros; inversion ID; subst.
  - exists z. inversion RED. assumption.
  - inversion RED; destruct H3; eauto.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  induction e; intros; inversion ID; subst; intuition.
  - inversion H. apply UNDEF with (z:=z). assumption.
  - inversion H; apply H1 with (z:=za); assumption.
  - inversion H; apply H1 with (z:=zb); assumption.
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z)
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z1.
  generalize dependent z2.
  induction e; intros.
  - inversion E1; inversion E2; subst. reflexivity.
  - inversion E1; inversion E2; subst. apply (state_deterministic Z s i z1 z2); assumption.
  - inversion E1; subst; inversion E2; subst;
        try (rewrite (IHe1 za VALA za0 VALA0) in *; rewrite (IHe2 zb VALB zb0 VALB0) in *);
        try reflexivity;
        try contradiction.
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 / id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
  generalize dependent z.
  induction e; intros.
  - inversion EV. subst. apply bs_Nat.
  - inversion EV. subst. apply bs_Var.
    assert (H: i ? (Var i)). { constructor. }
    apply (FV i H). assumption.
  - inversion EV; subst;
    try (apply IHe1 in VALA; apply IHe2 in VALB; eauto;
        intros; apply FV; constructor; intuition).
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z),
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity) : expr_scope.

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  split; intros; auto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  split; intros; apply EQ; auto.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  split; intros.
  - apply EQ2. apply EQ1. assumption.
  - apply EQ1. apply EQ2. assumption.
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

Notation "C '<~' e" := (plug C e) (at level 43, no associativity) : expr_scope.

Definition contextual_equivalent (e1 e2 : expr) : Prop :=
  forall (C : Context), (C <~ e1) ~~ (C <~ e2).

Notation "e1 '~c~' e2" := (contextual_equivalent e1 e2)
                            (at level 42, no associativity) : expr_scope.

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  unfold contextual_equivalent.
  unfold equivalent.
  split.
  - split; intros; generalize dependent n;
    induction C; intros; simpl; simpl in H0;
    try (apply H; assumption);
    try (inversion H0; subst; apply IHC in VALA; econstructor; eauto);
    try (inversion H0; subst; apply IHC in VALB; econstructor; eauto).
  - split; intros; apply (H (Hole)); simpl; assumption.
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
  where "st |- e --> e'" := (ss_step st e e') : expr_scope.

  #[export] Hint Constructors ss_step : core.

  Reserved Notation "st |- e -->> e'" (at level 0).

  Inductive ss_eval : state Z -> expr -> expr -> Prop :=
    se_Stop : forall (s : state Z)
                     (z : Z),  s |- (Nat z) -->> (Nat z)
  | se_Step : forall (s : state Z)
                     (e e' e'' : expr)
                     (HStep : s |- e --> e')
                     (Heval: s |- e' -->> e''), s |- e -->> e''
  where "st |- e -->> e'"  := (ss_eval st e e') : expr_scope.

  #[export] Hint Constructors ss_eval : core.

  Definition normal_form (e : expr) : Prop :=
    forall s, ~ exists e', (s |- e --> e').

  Lemma value_is_normal_form (e : expr) (HV: is_value e) : normal_form e.
  Proof.
    unfold normal_form. unfold not. intros.
    inversion HV. inversion H. rewrite <- H0 in H1. inversion H1.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    unfold normal_form. unfold not. intro.
    assert (NF: is_value (Nat 42 [/] Nat 0)).
    + apply H.  intros. inversion H0. inversion H1; subst.
      - inversion LEFT.
      - inversion RIGHT.
      - inversion EVAL; subst. inversion VALB; subst. contradiction.
    + inversion NF.
  Qed.

  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof.
    intro.
    remember (Nat 1 [+] Nat 1 [*] Nat 1 [+] Nat 1).
    remember (Nat (1 + 1) [*] Nat 1 [+] Nat 1).
    remember (Nat 1 [+] Nat 1 [*] Nat (1 + 1) ).
    remember ([] : state Z).
    assert (e0 <> e1). { rewrite Heqe0, Heqe1. intuition. inversion H0. }
    apply H0. apply (H e e0 e1 s); rewrite Heqe.
    - rewrite Heqe0. apply ss_Left. auto.
    - rewrite Heqe1. apply ss_Right. auto.
  Qed.

  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1; subst. inversion H2; subst.
    - remember (state_deterministic Z s i z z0 VAL VAL0).
      subst. reflexivity.
    - inversion H2; subst.
      + inversion LEFT.
      + inversion RIGHT.
      + remember (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z0 EVAL EVAL0).
        subst. reflexivity.
  Qed.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval.
    - constructor.
    - assumption.
  Qed.

  Lemma ss_eval_bop_equiv (s : state Z)
                      (za zb z : Z)
                      (e1 e2 : expr)
                      (op : bop)
                      (VALA : s |- e1 -->> (Nat za))
                      (VALB : s |- e2 -->> (Nat zb))
                      (EVAL : [| Bop op (Nat za) (Nat zb) |] s => z) :
    s |- (Bop op e1 e2) -->> (Nat z).
  Proof.
    induction VALA.
    - induction VALB.
      + eapply se_Step. apply ss_Bop. apply EVAL. apply se_Stop.
      + eapply se_Step. apply ss_Right. apply HStep.
        apply IHVALB. apply EVAL.
    - eapply se_Step. apply ss_Left. apply HStep. apply IHVALA.
      apply VALB. apply EVAL.
  Qed.

  Require Import Coq.Program.Equality.
  (* Застряли вместе с ДЮ *)
  Lemma eval_ss_bop_equiv (st : state Z)
                        (z : Z)
                        (e1 e2 : expr)
                        (op : bop)
                        (VAL : st |- Bop op e1 e2 -->> (Nat z)) :
    exists za zb, [| Bop op (Nat za) (Nat zb)|] st => z /\ st |- e1 -->> (Nat za) /\ st |- e2 -->> (Nat zb).
  Proof.
  (* eexists. eexists. split. *)
  inversion VAL. subst. inversion Heval. subst.
    + inversion HStep. subst. exists zl. exists zr. split.
      * apply EVAL.
      * split. constructor. constructor.
    + subst.
  (* remember (Bop op e1 e2) as e.
  remember (Nat z). *)
  Print ss_eval_ind.
  dependent induction VAL.
  (* - inversion Heqe. *)
  inversion HStep; subst.
  - specialize (IHVAL z l' e2 op).
  (* - eapply (IHVAL z l' e2 op). *)
  Admitted.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (s |- e -->> (Nat z)).
  Proof.
    split; intros; generalize dependent z.
    - induction e; intros; inversion H; subst.
      { constructor. }
      { eapply se_Step; [ constructor; apply VAR | auto ]. }
      all: apply IHe1 in VALA; apply IHe2 in VALB; eapply ss_eval_bop_equiv;
            [apply VALA | apply VALB | auto; econstructor; auto ].
    - induction e; intros; inversion H; subst.
      { constructor. }
      { inversion HStep. }
      { inversion HStep. subst.  inversion Heval; subst.
        { constructor. apply VAL. }
        { inversion HStep0. } }
      { apply eval_ss_bop_equiv in H. inversion_clear H. inversion_clear H0.
        specialize (IHe1 x). specialize (IHe2 x0).
        inversion_clear H. inversion_clear H1.
        apply IHe1 in H. apply IHe2 in H2.
        inversion H0; inversion VALA; inversion VALB; subst; econstructor; eauto. }
  Qed.
End SmallStep.

Module Renaming.

  Definition renaming := { f : id -> id | Bijective f }.

  Definition rename_id (r : renaming) (x : id) : id :=
    match r with
      exist _ f _ => f x
    end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.

  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof.
    destruct r. inversion b. inversion H.
    assert (B: Bijective x0). { unfold Bijective. exists x. split; assumption. }
    exists (exist _ x0 B). unfold renamings_inv. intros. simpl. auto.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r. inversion b. inversion H.
    assert (B: Bijective x0). { unfold Bijective. exists x. split; assumption. }
    exists (exist _ x0 B). unfold renamings_inv. intros. simpl. auto.
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
    unfold renamings_inv in Hinv. induction e.
    - auto.
    - simpl. rewrite Hinv. reflexivity.
    - simpl. rewrite IHe1, IHe2. reflexivity.
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
    - auto.
    - destruct a, r, r'. simpl. rewrite IHst, Hinv. reflexivity.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    destruct BH. destruct H. unfold Injective. intros.
    rewrite <- (H x0), H1, H. reflexivity.
  Qed.

  Lemma state_renamning_invariance (x : id) (st : state Z) (z : Z) (r : renaming) :
    st / x => z <-> (rename_state r st) / (rename_id r x) => z.
  Proof.
    split; intros.
    - induction st; inversion H; subst; destruct r; simpl; constructor.
        * unfold not in *. intros. apply H2. apply (bijective_injective x0); assumption.
        * apply IHst. assumption.
    - generalize dependent z.
      induction st; intros; inversion H; subst.
      * destruct a, r. simpl in *.
        inversion H1; subst. apply (bijective_injective x0) in H2.
        subst. constructor. apply b.
      * destruct a. destruct r eqn:R. simpl in *.
        inversion H0; subst.
        assert (x <> i).
        { unfold not in *. intros. destruct H1. f_equal. apply H3. }
        apply st_binds_tl. apply H3.
        apply IHst. auto.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    constructor; intros.
    - induction H.
      all: try (econstructor; [ apply IHeval1 | apply IHeval2 | .. ]; repeat assumption).
      + constructor.
      + constructor. apply state_renamning_invariance. apply VAR.
    - generalize dependent z. induction e; intros.
      + inversion H; subst. constructor.
      + inversion H; subst. constructor. eapply state_renamning_invariance. apply VAR.
      + inversion H; subst; try (econstructor; [ apply IHe1 | apply IHe2 | ..]; eauto).
  Qed.

End Renaming.
