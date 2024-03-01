Require Import BinInt ZArith_dec.
Require Export Id.
Require Export State.
Require Export Lia.

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

#[export] Hint Constructors eval.

(*
Module SmallStep.

  Inductive R : Set := Expr : expr -> R | Num : Z -> R.
    
  Inductive ss_eval : expr -> state Z -> R -> Prop :=
    ss_Nat          : forall (s : state Z) (n     : Z), ss_eval (Nat n) s (Num n)
  | ss_Var          : forall (s : state Z) (i     : id) (z : Z) (VAR : s / i => z), ss_eval (Var i) s (Num z)

  | ss_Or           : forall (s : state Z) (b : expr), ss_eval ((Nat Z.one)  [\/] b) s (Num Z.one)                                                                | ss_And          : forall (s : state Z) (b : expr), ss_eval ((Nat Z.zero) [&] b) s (Num Z.zero)                                                                                            
  | ss_Bop          : forall (o : bop) (s : state Z) (za zb zc : Z) (EVAL : [|Bop o (Nat za) (Nat zb)|] s => zc) (OP : o <> Or /\ o <> And),
                        ss_eval (Bop o (Nat za) (Nat zb)) s (Num zc)
                                                                
  | ss_Bop_RCompl   : forall (o : bop) (s : state Z) (za zb : Z) (b    : expr) (EVALB : ss_eval b s (Num  zb)),
                        ss_eval (Bop o (Nat za) b) s (Expr (Bop o (Nat za) (Nat zb)))
  | ss_Bop_RIncompl : forall (o : bop) (s : state Z) (za    : Z) (b b' : expr) (EVALB : ss_eval b s (Expr b')),
                        ss_eval (Bop o (Nat za) b) s (Expr (Bop o (Nat za) b'))
  | ss_Bop_LCompl   : forall (o : bop) (s : state Z) (za    : Z) (a b  : expr) (EVALA : ss_eval a s (Num  za)),
                        ss_eval (Bop o a b) s (Expr (Bop o (Nat za) b))
  | ss_Bop_LIncompl : forall (o : bop) (s : state Z) (a b a' : expr)           (EVALA : ss_eval a s (Expr a')),
                        ss_eval (Bop o a b) s (Expr (Bop o a' b)).    

End SmallStep.
*)
Module SmokeTest.
            
  Lemma nat_always n (s : state Z) : [| Nat n |] s => n.
  Proof.
    apply bs_Nat.  
  Qed.
  
  Lemma double_and_sum (s : state Z) (e : expr) (z : Z)
        (HH : [| e [*] (Nat 2) |] s => z) :
    [| e [+] e |] s => z.
  Proof. 
    inversion HH. inversion VALB.
    replace (za * 2)%Z with (za + za)%Z.
    - apply bs_Add. 
      + assumption.
      + assumption.
    - lia.
  Qed.

End SmokeTest.

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
  induction RED.
    + inversion ID.
    + inversion ID. rewrite <- H1.
      econstructor. eassumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.
    + inversion ID. destruct H3.
      - remember (IHRED1 H3). assumption.
      - remember (IHRED2 H3). assumption.      
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable (e : expr) (s : state Z) (id : id)
      (ID : id ? e) (UNDEF : forall (z : Z), ~ (s / id => z)) :
  forall (z : Z), ~ ([| e |] s => z).
Proof. intros. intuition.
  remember (defined_expression e s z id H ID). 
  destruct e0. remember (UNDEF x s0). contradiction.  
Qed.

(* The evaluation relation is deterministic *)

Lemma eval_deterministic (e : expr) (s : state Z) (z1 z2 : Z) 
      (E1 : [| e |] s => z1) (E2 : [| e |] s => z2) :
  z1 = z2.
Proof.
  revert E1. revert E2. revert z1. revert z2. 
  induction e ; intros.
    - inversion E1. inversion E2. rewrite <- H2. assumption.
    - inversion E1. inversion E2. 
      apply (state_deterministic Z s i z1 z2 VAR VAR0).
    - inversion E1; subst b; inversion E2. 
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          rewrite -> e. rewrite -> e0. 
          reflexivity.  
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          rewrite -> e. rewrite -> e0. 
          reflexivity.  
        + reflexivity.  
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.  
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          lia.
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. contradiction.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. contradiction.
        + reflexivity.
        + reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. contradiction.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. contradiction.
        + reflexivity.        
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. reflexivity.
        + remember (IHe1 za za0 VALA VALA0). 
          remember (IHe2 zb zb0 VALB VALB0).
          subst zb0. subst za0. reflexivity.
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
  revert EV. revert z. induction e; intros.
    - inversion EV. apply bs_Nat.
    - inversion EV. remember (v_Var i).
      remember (FV i v). 
      remember (e z). destruct i1.
      remember (s0 VAR).
      apply (bs_Var). assumption.
    - admit.
Admitted.

Definition equivalent (e1 e2 : expr) : Prop :=
  forall (n : Z) (s : state Z), 
    [| e1 |] s => n <-> [| e2 |] s => n.
Notation "e1 '~~' e2" := (equivalent e1 e2) (at level 42, no associativity).

Lemma eq_refl (e : expr): e ~~ e.
Proof. constructor. 
  - auto.
  - auto.
Qed.

Lemma eq_symm (e1 e2 : expr) (EQ : e1 ~~ e2): e2 ~~ e1.
Proof. constructor; remember (EQ n s); destruct i; assumption.
Qed.

Lemma eq_trans (e1 e2 e3 : expr) (EQ1 : e1 ~~ e2) (EQ2 : e2 ~~ e3):
  e1 ~~ e3.
Proof.
  constructor; remember (EQ1 n s); remember (EQ2 n s);
  destruct i; destruct i0; auto.
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

Lemma eq_eq_ceq (e1 e2 : expr) :
  e1 ~~ e2 <-> e1 ~c~ e2.
Proof. admit. Admitted. 

Module SmallStep.

  Inductive is_value : expr -> Prop :=
    isv_Intro : forall n, is_value (Nat n).

  Reserved Notation "st |- e --> e'" (at level 0).

  Inductive ss_eval : state Z -> expr -> expr -> Prop :=
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
  where "st |- e --> e'" := (ss_eval st e e').

  Lemma no_step_from_value (e : expr) (HV: is_value e) : ~ forall s, exists e', (s |- e --> e').
  Proof. intuition. revert H. admit. Admitted.
  
  Lemma ss_nondeterministic : ~ forall (e e' e'' : expr) (s : state Z), s |- e --> e' -> s |- e --> e'' -> e' = e''.
  Proof. intuition. admit. Admitted.
  
  Lemma ss_deterministic_step (e e' : expr)
                         (s    : state Z)
                         (z z' : Z)
                         (H1   : s |- e --> (Nat z))
                         (H2   : s |- e --> e') : e' = Nat z.
  Proof.
    inversion H1. 
      - subst e. inversion H2.
        remember (state_deterministic Z s i z z1 VAL VAL0).
        rewrite <- e. reflexivity.
      - subst e. inversion H2. 
        + remember (isv_Intro zl).
          remember (no_step_from_value (Nat zl) i).
          auto. admit.  
        + admit.
        + remember (eval_deterministic (Bop op (Nat zl) (Nat zr)) s z z1 EVAL EVAL0).
          rewrite <- e. reflexivity.
  Admitted.

  Lemma ss_eval_equiv (e : expr)
                      (s : state Z)
                      (z : Z) : [| e |] s => z <-> (e = Nat z \/ s |- e --> (Nat z)).
  Proof. admit. Admitted.


(*
  s |- e -> .... -> Nat z
       \
        \-> .... -> Nat z

  s |- e -> .... -> e'  
*)
  
End SmallStep.
