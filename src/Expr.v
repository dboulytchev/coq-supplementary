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
    apply bs_Nat.
  Qed.

  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof.
    inversion HH.
    inversion VALB.
    rewrite <- H6 in H3.
    assert(mul_2 : forall (v : Z), (v * 2%Z)%Z = (v + v)%Z).
    intros v.
    assert(make_2 : (1 + 1)%Z = 2%Z). simpl. reflexivity.
    rewrite <- make_2. rewrite -> Z.mul_add_distr_l. 
    rewrite -> Z.mul_1_r. reflexivity.
    rewrite -> (mul_2 za).
    apply bs_Add. assumption. assumption.
  Qed.

End SmokeTest.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (a b : expr) (op : bop), id ? a \/ id ? b -> id ? (Bop op a b)
where "x ? e" := (V e x).


Definition zle (z1 z2 : Z) : Z := 
  if Z.leb z1 z2 then Z.one else Z.zero.

Definition zlt (z1 z2 : Z) : Z :=
  if Z.ltb z1 z2 then Z.one else Z.zero.

Definition zge (z1 z2 : Z) : Z :=
  if Z.geb z1 z2 then Z.one else Z.zero.

Definition zgt (z1 z2 : Z) : Z :=
  if Z.gtb z1 z2 then Z.one else Z.zero.

Definition zeq (z1 z2 : Z) : Z :=
  if Z.eqb z1 z2 then Z.one else Z.zero.

Definition zne (z1 z2 : Z) : Z :=
  if Z.eqb z1 z2 then Z.zero else Z.one.

Definition zand (z1 z2 : Z) : Z :=
  (z1 * z2)%Z.

Fixpoint apply_bop (b : bop) (z1 : Z) (z2 : Z) : Z := 
  match b with 
  | Add => (z1 + z2)%Z 
  | Sub => (z1 - z2)%Z  
  | Mul => (z1 * z2)%Z  
  | Div => (Z.div z1 z2)%Z  
  | Mod => (Z.modulo z1 z2)%Z  
  | Le  => zle z1 z2
  | Lt  => zlt z1 z2
  | Ge  => zge z1 z2
  | Gt  => zgt z1 z2
  | Eq  => zeq z1 z2
  | Ne  => zne z1 z2
  | And => zand z1 z2
  | Or  => zor z1 z2
  end.

Lemma defined_subexpr
      (e1 e2 : expr) (s : state Z) (b : bop) (z : Z) 
      (H : [| Bop b e1 e2 |] s => z) :
  (exists z1 z2, [| e1 |] s => z1 /\ [| e2 |] s => z2 /\ z = apply_bop b z1 z2).
Proof.
  inversion H; 
  (* prove for all non-boolean ops *)
  exists za; exists zb; split; 
  try assumption; split; try assumption; unfold apply_bop; try reflexivity.
  (* prove for all comparisons *)
  - apply Z.leb_le in OP. unfold zle. rewrite -> OP. reflexivity.
  - apply Z.gt_lt in OP. apply Z.leb_gt in OP. unfold zle. 
    rewrite -> OP. reflexivity.
  - apply Z.ltb_lt in OP. unfold zlt. rewrite -> OP. reflexivity.
  - apply Z.ge_le in OP. apply Z.ltb_ge in OP. unfold zlt. rewrite -> OP. 
    reflexivity.
  - apply Z.ge_le in OP. apply Z.leb_le in OP. rewrite <- Z.geb_leb in OP. 
    unfold zge. rewrite -> OP. reflexivity.
  - apply Z.leb_gt in OP. unfold zge. rewrite -> Z.geb_leb. rewrite -> OP.
    reflexivity.
  - apply Z.gt_lt in OP. apply Z.gtb_lt in OP. unfold zgt. rewrite -> OP.
    reflexivity.
  - apply Z.ltb_ge in OP. unfold zgt. rewrite -> Z.gtb_ltb. rewrite -> OP.
    reflexivity.
  - unfold Z.eq in OP. apply Z.eqb_eq in OP. unfold zeq. rewrite -> OP. 
    reflexivity.
  - unfold Z.eq in OP. apply Z.eqb_neq in OP.  unfold zeq. rewrite -> OP. 
    reflexivity.
  - unfold Z.eq in OP. apply Z.eqb_neq in OP.  unfold zne. rewrite -> OP. 
    reflexivity.
  - unfold Z.eq in OP. apply Z.eqb_eq in OP.  unfold zne. rewrite -> OP. 
    reflexivity.
Qed.

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
  induction e as [n | x | b e1 IH1 e2 IH2].
  - inversion ID.
  - inversion ID as [x' x'_eq_x  x_eq_id | ].
    intros z RED.
    inversion RED.
    exists z. assumption.
  - intros z RED. apply defined_subexpr in RED. 
    inversion RED as [z1 [z2 [RED1 [RED2 Heq]]]].
    inversion ID as [ | id' e1' e2' b' [id_in_e1 | id_in_e2]].
    + apply IH1 with (z:=z1) in id_in_e1. assumption. assumption.
    + apply IH2 with (z:=z2) in id_in_e2. assumption. assumption.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof.
  induction e as [n | x | b e1 IH1 e2 IH2].
  - inversion ID.
  - inversion ID as [id' | ].
    intros z RED. inversion RED.
    pose proof (UNDEF z) as contra.
    contradiction.
  - intros z RED. apply defined_subexpr in RED. 
    inversion RED as [z1 [z2 [RED1 [RED2 Heq]]]].
    inversion ID as [ | id' e1' e2' b' [ID1 | ID2]].
    + apply IH1 with (z:=z1) in ID1. contradiction.
    + apply IH2 with (z:=z2) in ID2. contradiction.
Qed.


(* The evaluation relation is deterministic *)
Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  generalize dependent z2.
  generalize dependent z1.
  induction e as [n | x | b e1 IH1 e2 IH2].
  - assert (eval_Z : forall z s' z', [| Nat z |] s' => z' -> z = z'). 
    { intros z s' z' H. inversion H. reflexivity. }
    intros z1 E1 z2 E2.
    apply eval_Z in E1. apply eval_Z in E2. apply eq_trans with (n). 
    symmetry. assumption. assumption.
  - assert (eval_Var : forall x' s' z, [| Var x' |] s' => z -> (s' / x' => z)). 
    { intros x' s' z H. inversion H. assumption. }
    intros z1 E1 z2 E2.
    apply eval_Var in E1. apply eval_Var in E2.
    apply state_deterministic with (s) (x). assumption. assumption.
  - intros z1 E1 z2 E2.
    apply defined_subexpr in E1. inversion E1 as [z1' [z2' [E1' [E2' Heq']]]].
    apply defined_subexpr in E2. inversion E2 as [z1'' [z2'' [E1'' [E2'' Heq'']]]].
    apply IH1 with (z1:=z1'') in E1'.
    apply IH2 with (z1:=z2'') in E2'.
    rewrite -> E1' in Heq''. rewrite -> E2' in Heq''. 
    apply eq_trans with (apply_bop b z1' z2').
    assumption. symmetry. assumption. assumption. assumption.
Qed.

(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 /id => z <-> s2 / id => z.

Lemma variable_relevance (e : expr) (s1 s2 : state Z) (z : Z)
      (FV : forall (id : id) (ID : id ? e),
          equivalent_states s1 s2 id)
      (EV : [| e |] s1 => z) :
  [| e |] s2 => z.
Proof.
  generalize dependent z.
  induction e  as [n | x | b e1 IH1 e2 IH2].
  - intros z H. inversion H. apply bs_Nat.
  - intros z H. inversion H. apply bs_Var.
    specialize (FV x). 
    pose proof (v_Var x) as FV'. apply FV in FV'.
    unfold equivalent_states in FV'.
    specialize (FV' z). apply FV'. assumption.
  - assert (FV1 : forall id : id, (id ? e1) -> equivalent_states s1 s2 id).
    { intros id H. apply FV. apply v_Bop. left. assumption. }
    assert (FV2 : forall id : id, (id ? e2) -> equivalent_states s1 s2 id).
    { intros id H. apply FV. apply v_Bop. right. assumption. }
    intros z EV. destruct b; inversion EV; 
    [    apply bs_Add |
         apply bs_Sub |
         apply bs_Mul |
         apply bs_Div |
         apply bs_Mod |
         apply bs_Le_T with (za) (zb) |
         apply bs_Le_F with (za) (zb) |
         apply bs_Lt_T with (za) (zb) |
         apply bs_Lt_F with (za) (zb) |
         apply bs_Ge_T with (za) (zb) |
         apply bs_Ge_F with (za) (zb) |
         apply bs_Gt_T with (za) (zb) |
         apply bs_Gt_F with (za) (zb) |
         apply bs_Eq_T with (za) (zb) |
         apply bs_Eq_F with (za) (zb) |
         apply bs_Ne_T with (za) (zb) |
         apply bs_Ne_F with (za) (zb) |
         apply bs_And |
         apply bs_Or
    ];
    apply IH1 in VALA; apply IH2 in VALB; 
    assumption.
Qed.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. 
  unfold equivalent.
  intros n s. apply iff_refl.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof.
  unfold equivalent in EQ. unfold equivalent.
  intros n s. apply iff_sym. apply EQ.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  unfold equivalent in EQ1. unfold equivalent in EQ2. unfold equivalent.
  intros n s. apply iff_trans with ([|e2|] s => (n)).
  apply EQ1. apply EQ2.
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

Ltac my_inv H b za zb := intros H; destruct b; inversion H; [
         apply bs_Add |
         apply bs_Sub |
         apply bs_Mul |
         apply bs_Div |
         apply bs_Mod |
         apply bs_Le_T with (za) (zb) |
         apply bs_Le_F with (za) (zb) |
         apply bs_Lt_T with (za) (zb) |
         apply bs_Lt_F with (za) (zb) |
         apply bs_Ge_T with (za) (zb) |
         apply bs_Ge_F with (za) (zb) |
         apply bs_Gt_T with (za) (zb) |
         apply bs_Gt_F with (za) (zb) |
         apply bs_Eq_T with (za) (zb) |
         apply bs_Eq_F with (za) (zb) |
         apply bs_Ne_T with (za) (zb) |
         apply bs_Ne_F with (za) (zb) |
         apply bs_And |
         apply bs_Or
       ].

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof.
  unfold contextual_equivalent. unfold equivalent.
  split; intros H.
  - 

    induction C as [ | b C' IH e' | b e' C' IH].
    + unfold plug. assumption.
    + intros n s. simpl.
      split.
       * my_inv H1 b za zb; apply IH in VALA; assumption.
       * my_inv H1 b za zb; apply IH in VALA; assumption.
    + intros n s. simpl.
      split.
       * my_inv H1 b za zb; apply IH in VALA; assumption.
       * my_inv H1 b za zb; apply IH in VALA; assumption.
  - specialize (H Hole). unfold plug in H. assumption.
Qed.