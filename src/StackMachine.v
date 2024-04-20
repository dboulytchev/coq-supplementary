Require Import BinInt ZArith_dec.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Import Coq.Program.Equality.

Require Export Id.
Require Export State.
Require Export Expr.
Require Export Stmt.

(* Configuration *)
Definition conf := (list Z * state Z * list Z * list Z)%type.

(* Straight-line code (no if-while) *)
Module StraightLine.

  (* Straigh-line statements *)
  Inductive StraightLine : stmt -> Set :=
  | sl_Assn  : forall x e, StraightLine (x ::= e)
  | sl_Read  : forall x  , StraightLine (READ x)
  | sl_Write : forall e  , StraightLine (WRITE e)
  | sl_Skip  : StraightLine SKIP
  | sl_Seq   : forall s1 s2 (SL1 : StraightLine s1) (SL2 : StraightLine s2),
      StraightLine (s1 ;; s2).

  (* Instructions *)
  Inductive insn : Set :=
  | R  : insn
  | W  : insn
  | C  : Z -> insn
  | L  : id -> insn
  | S  : id -> insn
  | B  : bop -> insn.

  (* Program *)
  Definition prog := list insn.

  (* Big-step evaluation relation*)
  Reserved Notation "c1 '--' q '-->' c2" (at level 0).
  Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

  Inductive sm_int : conf -> prog -> conf -> Prop :=
  | sm_End   : forall (p : prog) (c : conf),
      c -- [] --> c

  | sm_Read  : forall (q : prog) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (z::s, m, i, o) -- q --> c'),
      (s, m, z::i, o) -- R::q --> c'

  | sm_Write : forall (q : prog) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (s, m, i, z::o) -- q --> c'),
      (z::s, m, i, o) -- W::q --> c'

  | sm_Load  : forall (q : prog) (x : id) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (VAR : m / x => z)
                      (EXEC : (z::s, m, i, o) -- q --> c'),
      (s, m, i, o) -- (L x)::q --> c'

  | sm_Store : forall (q : prog) (x : id) (z : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (s, m [x <- z], i, o) -- q --> c'),
      (z::s, m, i, o) -- (S x)::q --> c'

  | sm_Add   : forall (p q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x + y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Add)::q --> c'

  | sm_Sub   : forall (p q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x - y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Sub)::q --> c'

  | sm_Mul   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x * y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Mul)::q --> c'

  | sm_Div   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (NZERO : ~ y = Z.zero)
                      (EXEC : ((Z.div x y)::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Div)::q --> c'

  | sm_Mod   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (NZERO : ~ y = Z.zero)
                      (EXEC : ((Z.modulo x y)::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Mod)::q --> c'

  | sm_Le_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.le x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Le)::q --> c'

  | sm_Le_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.gt x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Le)::q --> c'

  | sm_Ge_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.ge x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ge)::q --> c'

  | sm_Ge_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.lt x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ge)::q --> c'

  | sm_Lt_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.lt x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Lt)::q --> c'

  | sm_Lt_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.ge x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Lt)::q --> c'

  | sm_Gt_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.gt x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Gt)::q --> c'

  | sm_Gt_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.le x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Gt)::q --> c'

  | sm_Eq_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.eq x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Eq)::q --> c'

  | sm_Eq_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : ~ Z.eq x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Eq)::q --> c'

  | sm_Ne_T  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : ~ Z.eq x y)
                      (EXEC : (Z.one::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ne)::q --> c'

  | sm_Ne_F  : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (OP : Z.eq x y)
                      (EXEC : (Z.zero::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Ne)::q --> c'

  | sm_And   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (BOOLX : zbool x)
                      (BOOLY : zbool y)
                      (EXEC : ((x * y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B And)::q --> c'

  | sm_Or    : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (BOOLX : zbool x)
                      (BOOLY : zbool y)
                      (EXEC : ((zor x y)::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Or)::q --> c'

  | sm_Const : forall (q : prog) (n : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : (n::s, m, i, o) -- q --> c'),
      (s, m, i, o) -- (C n)::q --> c'
  where "c1 '--' q '-->' c2" := (sm_int c1 q c2).

  (* Expression compiler *)
  Fixpoint compile_expr (e : expr) :=
  match e with
  | Var  x       => [L x]
  | Nat  n       => [C n]
  | Bop op e1 e2 => compile_expr e1 ++ compile_expr e2 ++ [B op]
  end.

  (* Partial correctness of expression compiler *)
  Lemma compiled_expr_correct_cont
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (p : prog) (c : conf)
        (VAL : [| e |] st => n)
        (EXEC: (n::s, st, i, o) -- p --> c) :
    (s, st, i, o) -- (compile_expr e) ++ p --> c.
  Proof.
    dependent induction e; dependent destruction VAL.

    constructor. assumption.
    econstructor. eassumption. assumption.

    all: simpl;
         rewrite app_ass; eapply IHe1; [ eassumption | ];
         rewrite app_ass; eapply IHe2; [ eassumption | ];
         constructor; assumption; assumption.
  Qed.

  #[export] Hint Resolve compiled_expr_correct_cont.

  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof.
    rewrite (app_nil_end (compile_expr e)).
    apply (compiled_expr_correct_cont _ _ _ _ _ n nil).
    assumption. constructor. constructor.
  Qed.

  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof.
    dependent induction e; try dependent destruction b.
    * dependent destruction EXEC. exists z. auto.
    * dependent destruction EXEC. exists z. auto.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Add] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Add :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2. exists (x + x0)%Z. constructor; try constructor; assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Sub] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Sub :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2. exists (x - x0)%Z. constructor; try constructor; assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Mul] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Mul :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2. exists (x * x0)%Z. constructor; try constructor; assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Div] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Div :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2. exists (Z.div x x0)%Z. constructor; try constructor; assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Mod] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Mod :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2. exists (x mod x0)%Z. constructor; try constructor; assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Le] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Le :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2.
      - exists Z.one. constructor; try assumption. apply (bs_Le_T _ _ _ x x0); assumption.
      - exists Z.zero. constructor; try assumption. apply (bs_Le_F _ _ _ x x0); assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Lt] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Lt :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2.
      - exists Z.one. constructor; try assumption. apply (bs_Lt_T _ _ _ x x0); assumption.
      - exists Z.zero. constructor; try assumption. apply (bs_Lt_F _ _ _ x x0); assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Ge] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Ge :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2.
      - exists Z.one. constructor; try assumption. apply (bs_Ge_T _ _ _ x x0); assumption.
      - exists Z.zero. constructor; try assumption. apply (bs_Ge_F _ _ _ x x0); assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Gt] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Gt :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2.
      - exists Z.one. constructor; try assumption. apply (bs_Gt_T _ _ _ x x0); assumption.
      - exists Z.zero. constructor; try assumption. apply (bs_Gt_F _ _ _ x x0); assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Eq] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Eq :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2.
      - exists Z.one. constructor; try assumption. apply (bs_Eq_T _ _ _ x x0); assumption.
      - exists Z.zero. constructor; try assumption. apply (bs_Eq_F _ _ _ x x0); assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Ne] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Ne :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2.
      - exists Z.one. constructor; try assumption. apply (bs_Ne_T _ _ _ x x0); assumption.
      - exists Z.zero. constructor; try assumption. apply (bs_Ne_F _ _ _ x x0); assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B And] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B And :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2. exists (x * x0)%Z. constructor; try constructor; assumption.
    * simpl in EXEC. repeat rewrite app_ass in EXEC.
      assert (H1 : exists n : Z, [|e1|] st => (n) /\ ((n :: s, st, i, o))
        -- compile_expr e2 ++ [B Or] ++ p --> (c)).
      apply IHe1. assumption. dependent destruction H1. dependent destruction H.
      assert (H2 : exists n : Z, [|e2|] st => (n) /\ (n :: x :: s, st, i, o) -- B Or :: p --> c).
      apply IHe2. assumption. dependent destruction H2. dependent destruction H1.
      dependent destruction H2. exists (zor x x0)%Z. constructor; try constructor; assumption.
  Qed.

  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof.
    assert (H : exists n' : Z, [|e|] st => n' /\ (n'::s, st, i, o) -- [] --> (n::s, st, i, o)).
    - apply compiled_expr_not_incorrect_cont. rewrite <- app_nil_end. assumption.
    - dependent destruction H. dependent destruction H. dependent destruction H0. assumption.
  Qed.

  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof. constructor. apply compiled_expr_not_incorrect. apply compiled_expr_correct. Qed.

  Fixpoint compile (s : stmt) (H : StraightLine s) : prog :=
    match H with
    | sl_Assn x e          => compile_expr e ++ [S x]
    | sl_Skip              => []
    | sl_Read x            => [R; S x]
    | sl_Write e           => compile_expr e ++ [W]
    | sl_Seq s1 s2 sl1 sl2 => compile s1 sl1 ++ compile s2 sl2
    end.

  Lemma compiled_straightline_correct_cont
        (p : stmt) (Sp : StraightLine p) (st st' : state Z)
        (i o i' o' : list Z) (q : prog) (c : conf)
        (H : (st, i, o) == p ==> (st', i', o'))
        (EXEC : ([], st', i', o') -- q --> c) :
    ([], st, i, o) -- (compile p Sp) ++ q --> c.
  Proof.
    dependent induction p; dependent destruction Sp; dependent destruction H.
    * assumption.
    * simpl. rewrite app_ass. apply (compiled_expr_correct_cont _ _ _ _ _ z). assumption.
      constructor. assumption.
    * constructor. constructor. assumption.
    * simpl. rewrite app_ass. apply (compiled_expr_correct_cont _ _ _ _ _ z). assumption.
      constructor. assumption.
    * dependent destruction c'. dependent destruction p. simpl. rewrite app_ass.
      apply (IHp1 _ _ s _ _ l l0). assumption.
      apply (IHp2 _ _ st' _ _ i' o'). assumption.
      assumption.
  Qed.

  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    rewrite (app_nil_end (compile _ _)).
    apply (compiled_straightline_correct_cont _ _ _ st' _ _ i' o' nil ([], st', i', o')).
    assumption. constructor. constructor.
  Qed.

  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof.
    dependent induction p; dependent destruction Sp; simpl in EXEC.
    * exists st, i, o. constructor. constructor. assumption.
    * assert (H : exists (n : Z), [| e |] st => n /\ ([n], st, i0, o) -- S i :: q --> c).
      - apply compiled_expr_not_incorrect_cont. rewrite app_ass in EXEC. assumption.
      - dependent destruction H. dependent destruction H. dependent destruction H0.
        exists st [i <- x], i0, o. constructor. constructor. assumption. assumption.
    * dependent destruction EXEC. dependent destruction EXEC.
      exists st [i <- z], i1, o. constructor. constructor. assumption.
    * assert (H : exists (n : Z), [| e |] st => n /\ ([n], st, i, o) -- W :: q --> c).
      - apply compiled_expr_not_incorrect_cont. rewrite app_ass in EXEC. assumption.
      - dependent destruction H. dependent destruction H. dependent destruction H0.
        exists st, i, (x :: o). constructor. constructor. assumption. assumption.
    * assert (H : exists (st' : state Z) (i' o' : list Z), (st, i, o) == p1 ==> (st', i', o')
        /\ ([], st', i', o') -- compile p2 Sp2 ++ q --> c).
      apply (IHp1 Sp1). rewrite app_ass in EXEC. assumption.
      dependent destruction H. dependent destruction H. dependent destruction H.
      dependent destruction H.
      assert (H2 : exists (st' : state Z) (i' o' : list Z), (x, x0, x1) == p2 ==> (st', i', o')
        /\ ([], st', i', o') -- q --> c).
      apply (IHp2 Sp2). assumption.
      dependent destruction H2. dependent destruction H1. dependent destruction H1.
      dependent destruction H1.
      exists x2, x3, x4. constructor. apply (bs_Seq _ (x, x0, x1)).
      assumption. assumption. assumption.
  Qed.

  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof.
    assert (H : exists (st'' : state Z) (i'' o'' : list Z), (st, i, o) == p ==> (st'', i'', o'')
        /\ ([], st'', i'', o'') -- [] --> ([], st', i', o')).
    * apply (compiled_straightline_not_incorrect_cont _ Sp). rewrite <- app_nil_end. assumption.
    * dependent destruction H. dependent destruction H. dependent destruction H.
      dependent destruction H. dependent destruction H0. assumption.
  Qed.

  Theorem straightline_compiler_correct
          (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z) :
    (st, i, o) == p ==> (st', i', o') <-> ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    constructor.
    apply compiled_straightline_correct.
    apply compiled_straightline_not_incorrect.
  Qed.

End StraightLine.

Inductive insn : Set :=
  JMP : nat -> insn
| JZ  : nat -> insn
| JNZ : nat -> insn
| LAB : nat -> insn
| B   : StraightLine.insn -> insn.

Definition prog := list insn.

Fixpoint at_label (l : nat) (p : prog) : prog :=
  match p with
    []          => []
  | LAB m :: p' => if eq_nat_dec l m then p' else at_label l p'
  | _     :: p' => at_label l p'
  end.

Notation "c1 '==' q '==>' c2" := (StraightLine.sm_int c1 q c2) (at level 0).
Reserved Notation "P '|-' c1 '--' q '-->' c2" (at level 0).

Inductive sm_int : prog -> conf -> prog -> conf -> Prop :=
| sm_Base      : forall (c c' c'' : conf)
                        (P p      : prog)
                        (i        : StraightLine.insn)
                        (H        : c == [i] ==> c')
                        (HP       : P |- c' -- p --> c''), P |- c -- B i :: p --> c''

| sm_Label     : forall (c c' : conf)
                        (P p  : prog)
                        (l    : nat)
                        (H    : P |- c -- p --> c'), P |- c -- LAB l :: p --> c'

| sm_JMP       : forall (c c' : conf)
                        (P p  : prog)
                        (l    : nat)
                        (H    : P |- c -- at_label l P --> c'), P |- c -- JMP l :: p --> c'

| sm_JZ_False  : forall (s i o : list Z)
                        (m     : state Z)
                        (c'    : conf)
                        (P p   : prog)
                        (l     : nat)
                        (z     : Z)
                        (HZ    : z <> 0%Z)
                        (H     : P |- (s, m, i, o) -- p --> c'), P |- (z :: s, m, i, o) -- JZ l :: p --> c'

| sm_JZ_True   : forall (s i o : list Z)
                        (m     : state Z)
                        (c'    : conf)
                        (P p   : prog)
                        (l     : nat)
                        (H     : P |- (s, m, i, o) -- at_label l P --> c'), P |- (0%Z :: s, m, i, o) -- JZ l :: p --> c'

| sm_JNZ_False : forall (s i o : list Z)
                        (m     : state Z)
                        (c'    : conf)
                        (P p   : prog)
                        (l     : nat)
                        (H : P |- (s, m, i, o) -- p --> c'), P |- (0%Z :: s, m, i, o) -- JNZ l :: p --> c'

| sm_JNZ_True  : forall (s i o : list Z)
                        (m     : state Z)
                        (c'    : conf)
                        (P p   : prog)
                        (l     : nat)
                        (z     : Z)
                        (HZ    : z <> 0%Z)
                        (H : P |- (s, m, i, o) -- at_label l P --> c'), P |- (z :: s, m, i, o) -- JNZ l :: p --> c'
| sm_Empty : forall (c : conf) (P : prog), P |- c -- [] --> c
where "P '|-' c1 '--' q '-->' c2" := (sm_int P c1 q c2).

Fixpoint label_occurs_once_rec (occured : bool) (n: nat) (p : prog) : bool :=
  match p with
    LAB m :: p' => if eq_nat_dec n m
                   then if occured
                        then false
                        else label_occurs_once_rec true n p'
                   else label_occurs_once_rec occured n p'
  | _     :: p' => label_occurs_once_rec occured n p'
  | []          => occured
  end.

Definition label_occurs_once (n : nat) (p : prog) : bool := label_occurs_once_rec false n p.

Fixpoint prog_wf_rec (prog p : prog) : bool :=
  match p with
    []      => true
  | i :: p' => match i with
                 JMP l => label_occurs_once l prog
               | JZ  l => label_occurs_once l prog
               | JNZ l => label_occurs_once l prog
               | _     => true
               end && prog_wf_rec prog p'
  end.

Definition prog_wf (p : prog) : bool := prog_wf_rec p p.

Lemma wf_app (p q  : prog)
             (l    : nat)
             (Hwf  : prog_wf_rec q p = true)
             (Hocc : label_occurs_once l q = true) : prog_wf_rec q (p ++ [JMP l]) = true.
Proof.
  induction p.
  { simpl. intuition. }
  { simpl in Hwf. destruct a; simpl; apply Bool.andb_true_iff in Hwf; inversion Hwf; intuition.
  }
Qed.

Fixpoint prog_labels (p : prog) : list nat :=
match p with
  [] => []
| i :: p => match i with
              JMP l => l :: prog_labels p
            | JZ  l => l :: prog_labels p
            | JNZ l => l :: prog_labels p
            | _     => prog_labels p
            end
end.

Lemma wf_lem (p q : prog)
    : (forall l, In l (prog_labels q) -> label_occurs_once l p = true) <-> prog_wf_rec p q = true.
Proof.
    split; intros.
    * dependent induction q; auto; dependent destruction a; simpl;
      unfold label_occurs_once in *; simpl in *; auto.
      all: rewrite H; auto.
    * dependent induction q; auto; dependent induction a; simpl in *; auto; destruct H0; auto.
      all: try dependent destruction H0; apply andb_prop in H; destruct H; auto.
Qed.

Lemma prog_labels_app p q : prog_labels (p ++ q) = prog_labels p ++ prog_labels q.
Proof. dependent induction p; auto; dependent destruction a; simpl; congruence. Qed.

Lemma prog_labels_rev p : prog_labels (rev p) = rev (prog_labels p).
Proof.
    dependent induction p; auto; dependent destruction a; simpl.
    all: rewrite prog_labels_app; simpl; rewrite <- IHp; auto.
    all: rewrite app_nil_r; auto.
Qed.

Lemma wf_rev (p q : prog) (Hwf : prog_wf_rec q p = true) : prog_wf_rec q (rev p) = true.
Proof. apply wf_lem. rewrite prog_labels_rev. intros. apply In_rev in H. eapply wf_lem; eauto. Qed.

Fixpoint convert_straightline (p : StraightLine.prog) : prog :=
  match p with
    []      => []
  | i :: p' => B i :: convert_straightline p'
  end.

Lemma cons_comm_app (A : Type) (a : A) (l1 l2 : list A) : l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  induction l1; auto.
  simpl. rewrite <- IHl1. reflexivity.
Qed.
  (*
Lemma straightline_wf_gen (p    : StraightLine.prog)
                          (q    : prog             )
                          (Hqwf : prog_wf_rec q q = true ) :
  prog_wf_rec q (q ++ convert_straightline p) = true.
Proof.
  generalize dependent q. induction p; intros q Hqwf.
  { simpl. rewrite app_nil_r. assumption. }
  { simpl. rewrite cons_comm_app.


    apply IHp.
    assert (A: prog_wf (B a :: q) = true).
      unfold prog_wf. simpl. induction q. auto.

    induction q.
    { simpl. unfold prog_wf. simpl. reflexivity. }
    { simpl. unfold prog_wf.

    Search list.
  { auto. }
  { simpl. unfold prog_wf. simpl.
    *)
Definition compile_expr (e : expr) : prog :=
  convert_straightline (StraightLine.compile_expr e).
