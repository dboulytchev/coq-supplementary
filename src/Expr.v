Require Import FinFun.
Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

Require Import List.
Import ListNotations.

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

  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof. apply bs_Nat. Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH; subst.
    inversion VALB; subst.
    rewrite Z.mul_comm.

    assert (HEE: [|e [+] e|] s => (za + za)).
      { apply (bs_Add s e e za za); assumption. }

    rewrite Z.add_diag in HEE.
    assumption.
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
  induction HSub; intros z H.
  - exists z. assumption.
  - inversion H; subst; apply IHHSub in VALA; assumption.
  - inversion H; subst; apply IHHSub in VALB; assumption.
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
  generalize dependent RED.
  generalize dependent s.
  generalize dependent z.
  generalize dependent e.
  intros e ID.
  induction e; intros z' s RED.
  - inversion ID.
  - inversion ID; subst; inversion RED; subst; exists z'; assumption.
  - inversion ID; inversion RED; subst;
    try (destruct H3; [ apply (IHe1 H _ _ VALA) | apply (IHe2 H _ _ VALB)  ]).
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  induction e; intros z'.
  - intros H. inversion H; subst; inversion ID.
  - intros H.
    inversion ID; subst.
    inversion H; subst.
    apply UNDEF in VAR. assumption.
  - inversion ID; subst.
    intros H.
    inversion H; subst; unfold not in *;
     try (destruct H3;
          [apply (IHe1 H0 _ VALA) | apply (IHe2 H0 _ VALB) ];
          assumption).
Qed.

(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z)
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z1.
  generalize dependent z2.

  induction e; intros z2 H2 z1 H1.
  - inversion H1; subst.
    inversion H2; subst.
    reflexivity.
  - inversion H1; subst.
    inversion H2; subst.
     apply (state_deterministic _ s i z1 z2); assumption.
  - inversion H1; subst;
    inversion H2; subst ;
    destruct (IHe1 za VALA za0 VALA0);
    destruct (IHe2 zb VALB zb0 VALB0);
    try reflexivity;
    try Lia.lia;
    try (apply OP0 in OP; destruct OP);
    try (apply OP in OP0; destruct OP0).
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z : Z, s1 /id => z <-> s2 / id => z.

  Ltac try_constrs za' zb' :=
    (* constructro workaround *)
    try (apply bs_Add);
    try (apply bs_Sub);
    try (apply bs_Mul);
    try (apply bs_Div);
    try (apply bs_Mod);
    try (apply bs_And);
    try (apply bs_Or);

    try (apply bs_Le_T with (za := za') (zb := zb'));
    try (apply bs_Le_F with (za := za') (zb := zb'));
    try (apply bs_Lt_T with (za := za') (zb := zb'));
    try (apply bs_Lt_F with (za := za') (zb := zb'));
    try (apply bs_Ge_T with (za := za') (zb := zb'));
    try (apply bs_Ge_F with (za := za') (zb := zb'));
    try (apply bs_Gt_T with (za := za') (zb := zb'));
    try (apply bs_Gt_F with (za := za') (zb := zb'));
    try (apply bs_Eq_T with (za := za') (zb := zb'));
    try (apply bs_Eq_F with (za := za') (zb := zb'));
    try (apply bs_Ne_T with (za := za') (zb := zb'));
    try (apply bs_Ne_F with (za := za') (zb := zb')).

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
  generalize dependent z.
  induction e; intros z' H.
  - inversion H; subst. apply bs_Nat.
  - inversion H; subst.
    specialize FV with i.

    assert (HFV: (i) ? (Var i)). { apply v_Var. }

    apply FV in HFV.
    unfold equivalent_states in HFV.
    apply HFV in VAR.

    apply bs_Var.
    assumption.
  - inversion H; subst;

    try (apply IHe1 in VALA;
        apply IHe2 in VALB;

        try_constrs za zb;
        try assumption;

        intros id;
        intros H';
        specialize FV with id;
        apply FV;
        constructor;
        [ right | left | right];
        assumption).
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z),
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof.
  induction e; unfold equivalent; intros n s; split; trivial.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent.
  induction e1;
  induction e2; split;
  intros H;
  unfold equivalent in *;
  apply EQ; assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in *.
  intros n s; split; intros H.

  - apply EQ2.
    apply EQ1.
    assumption.
  - apply EQ1.
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

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  split; unfold contextual_equivalent; intros H.
  - intros C. induction C; unfold equivalent; split; intros H'; simpl in *.
    (* TODO duplication *)
    + apply H. assumption.
    + apply H. assumption.
    + inversion H'; subst; inversion H'; subst; apply IHC in VALA0;
      try_constrs za0 zb0;
      try assumption.
    + inversion H'; subst; inversion H'; subst; apply IHC in VALA0;
      try_constrs za0 zb0;
      try assumption.
    + inversion H'; subst; inversion H'; subst; apply IHC in VALB0;
      try_constrs za0 zb0;
      try assumption.
    + inversion H'; subst; inversion H'; subst; apply IHC in VALB0;
      try_constrs za0 zb0;
      try assumption.
  - unfold equivalent. split; intros H';
      specialize H with Hole;
      simpl in H;
      apply H;
      assumption.
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
    unfold normal_form.
    unfold not.
    intros.
    inversion HV. subst.
    inversion H. inversion H0.
  Qed.

  Lemma normal_form_is_not_a_value : ~ forall (e : expr), normal_form e -> is_value e.
  Proof.
    unfold not.
    intros.
    unfold normal_form in H.
    specialize H with ((Nat 1) [/] (Nat 0)).

    assert (HA: (is_value (Nat 1 [/] Nat 0)) <-> False).
      { split.
        { intros. inversion H0. }
        { intros. inversion H0. } }

    apply HA.
    apply H.
    clear HA H.

    unfold not.
    intros.
    destruct H.
    inversion H; subst.
    { inversion LEFT. }
    { inversion RIGHT. }
    { inversion EVAL. subst.
      inversion VALB. subst. apply NZERO. reflexivity. }
  Qed.

  Lemma no_step_from_value (e : expr) (HV: is_value e) : forall s, ~ exists e', (s |- e --> e').
  Proof.
    intros s H.

    inversion HV; subst.
    destruct H.
    inversion H.
  Qed.

Definition zero_sum_contra: expr :=
  let z := Nat Z.zero in
  let z_sum := z [+] z in
  z_sum [+] z_sum.

  Lemma ss_eval_stops_at_value (st : state Z) (e e': expr) (Heval: st |- e -->> e') : is_value e'.
  Proof.
    induction Heval; subst.
    - constructor.
    - assumption.
  Qed.

Definition zero_sum_result_l: expr :=
  let z := Nat Z.zero in
  let z_sum := z [+] z in
  z [+] z_sum.

Definition zero_sum_result_r: expr :=
  let z := Nat Z.zero in
  let z_sum := z [+] z in
  z_sum [+] z .

Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z),
  s |- e --> e' -> s |- e --> e'' -> e' = e''.
Proof.
  unfold not.
  intros H.

  specialize H with
    (e := zero_sum_contra)
    (e' := zero_sum_result_l)
    (e'' := zero_sum_result_r)
    (s := []).

  (* duplication TODO *)
  assert (Hl: ([]) |- zero_sum_contra --> (zero_sum_result_l)).
    { unfold zero_sum_contra, zero_sum_result_l.
      apply ss_Left.
      apply ss_Bop.

      replace ([|Nat Z.zero [+] Nat Z.zero|] [] => (Z.zero))
        with  ([|Nat Z.zero [+] Nat Z.zero|] [] => (Z.add Z.zero Z.zero)).


      + apply bs_Add; apply bs_Nat.
      + reflexivity. }

  assert (Hr: ([]) |- zero_sum_contra --> (zero_sum_result_r)).
    { unfold zero_sum_contra, zero_sum_result_l.
      apply ss_Right.
      apply ss_Bop.

      replace ([|Nat Z.zero [+] Nat Z.zero|] [] => (Z.zero))
        with  ([|Nat Z.zero [+] Nat Z.zero|] [] => (Z.add Z.zero Z.zero)).


      + apply bs_Add; apply bs_Nat.
      + reflexivity. }

  apply H in Hl.
  - discriminate.
  - assumption.
Qed.

Lemma ss_deterministic_step (e e' : expr)
                        (s    : state Z)
                        (z z' : Z)
                        (H1   : s |- e --> (Nat z))
                        (H2   : s |- e --> e') : e' = Nat z.
Proof.
  inversion H1; subst.
  inversion H2; subst.

  - destruct (state_deterministic _ _ _ _ _ VAL VAL0). reflexivity.
  - inversion H2; subst.
    + inversion LEFT.
      (* that is not needed when now Equality imported *)
    +
      (* inversion H0. subst. *) (* TODO seems like bug in coq lsp *)
      inversion RIGHT.
    +
      (* TODO Require Import Coq.Program.Equality. problem *)
      destruct (eval_deterministic  _ _ _ _ EVAL EVAL0).
      reflexivity.
Qed.

Lemma ss_eval_equiv (e : expr)
                    (s : state Z)
                    (z : Z) : [| e |] s => z <-> (e = Nat z \/ s |- e --> (Nat z)).
Proof. admit. Admitted. (* ??? *)

End SmallStep.

Module Renaming.

  Definition renaming := { f : id -> id | Bijective f }.
  Print Bijective.

  Definition rename_id (r : renaming) (x : id) : id :=
    match r with exist _ f g => f x end.

  Definition renamings_inv (r r' : renaming) := forall (x : id), rename_id r (rename_id r' x) = x.

  Lemma renaming_inv (r : renaming) : exists (r' : renaming), renamings_inv r' r.
  Proof.
    unfold renamings_inv.
    destruct  r.
    inversion b.

    assert (HA: Bijective x0).
      { unfold Bijective.
        destruct H.

        exists x. auto. }

    unfold renaming.

    exists (exist Bijective x0 HA).
    intros. simpl. unfold rename_id.
    destruct H.
    auto.
  Qed.

  Lemma renaming_inv2 (r : renaming) : exists (r' : renaming), renamings_inv r r'.
  Proof.
    destruct r.
    inversion b.
    destruct H.

    assert (HA: Bijective x0).
      { unfold Bijective.
        exists x. auto. }

    exists (exist Bijective x0 HA).
    unfold renamings_inv. intro.
    simpl. auto.
  Qed.

  Lemma renaming_inv_inv r1 : exists r2, renamings_inv r1 r2 /\ renamings_inv r2 r1.
  Proof.
    unfold renamings_inv.
    destruct  r1.
    inversion b.

    assert (HA: Bijective x0).
      { unfold Bijective.
        exists x. split; destruct H; auto. }

    exists (exist Bijective x0 HA).

    split; (intros; simpl; destruct H; auto).
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
    - reflexivity.
    - simpl. rewrite Hinv. reflexivity.
    - simpl.
      rewrite IHe1, IHe2.
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
    induction st.
    - reflexivity.
    - simpl.
      destruct a. simpl.
      destruct r'. simpl.
      destruct r. simpl.

      rewrite IHst.
      clear IHst.
      rewrite Hinv.

      reflexivity.
  Qed.

  Lemma bijective_injective (f : id -> id) (BH : Bijective f) : Injective f.
  Proof.
    unfold Injective.
    unfold Bijective in BH.
    intros.
    destruct BH. destruct H0.

    eapply f_equal in H.
    do 2 erewrite H0 in H.

    assumption.
  Qed.

  Lemma eval_renaming_invariance (e : expr) (st : state Z) (z : Z) (r: renaming) :
    [| e |] st => z <-> [| rename_expr r e |] (rename_state r st) => z.
  Proof.
    split.
    - generalize dependent z; induction e; intros.
      + simpl.
        inversion H. subst.
        constructor.
      + simpl. unfold rename_id.
        destruct r.
        inversion H. subst.
        induction VAR; subst.
        { simpl. constructor. constructor. }
        { simpl.
          assert (HA: x id <> x id').
            { unfold not.
            intros.
            eapply bijective_injective in b as b'.
            apply b' in H1.
            contradiction H0. }

          constructor.
          eapply st_binds_tl.
          - assumption.
          - assert (HA': [|Var id|] st => x0).
              { constructor. assumption. }

             clear H VAR H0 HA.
             apply IHVAR in HA'. clear IHVAR.

             inversion HA'. subst.
             assumption. }

        + simpl. inversion H; subst;
          try (now
          apply IHe1 in VALA;
          apply IHe2 in VALB;
          econstructor; eassumption).
    - generalize dependent z. induction e; intros.
      + inversion H. subst. constructor.
      + simpl in H. inversion H; subst.

        dependent induction VAR.
        constructor.

        { destruct (renaming_inv r).

          clear H.
          eapply f_equal in x.

          assert (HA: st = rename_state x0 (rename_state r st)). {
            symmetry.
            eapply re_rename_state.
            assumption.
          }

          rewrite <- HA in x.
          rewrite <- x.
          simpl.
          destruct x0.
          unfold rename_id.
          destruct r.
          simpl.
          rewrite H0.
          constructor. }
        { destruct (renaming_inv_inv r).

          assert (HA: st = rename_state x0 (rename_state r st)). {
            symmetry.
            eapply re_rename_state.
            destruct H1.
            assumption.
          }

          eapply f_equal in x.
          rewrite <- HA in x.

          rewrite <- x.
          simpl. destruct x0.

          constructor.
          apply st_binds_tl.
          { unfold not in *.
            intros.
            apply H0.
            rewrite H2. clear H2.
            unfold rename_id. destruct r.

            destruct H1.
            apply H1. }
          { assert (HA': [|Var i|] ((rename_state (exist (fun f : id -> id => Bijective f) x0 b) st0)) => (z) ->
              st_binds Z (rename_state (exist (fun f : id -> id => Bijective f) x0 b) st0) i z).

              { intros. inversion H2. subst. assumption. }
              apply HA'. clear HA'.

              eapply IHVAR with r.
              + simpl.
                rewrite re_rename_state.
                { constructor. assumption. }
                destruct H1. auto.
              + reflexivity.
              + rewrite re_rename_state.
                { reflexivity. }
                destruct H1. auto.
              + reflexivity.
              + reflexivity. } (* TODO how to write it with `all` ?*)
        }
      + simpl in H.
        inversion H; subst; try (now
        apply IHe1 in VALA;
        apply IHe2 in VALB;
        econstructor; eassumption).
  Qed.

End Renaming.
