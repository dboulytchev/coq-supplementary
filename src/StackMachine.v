Require Import BinInt ZArith_dec.
Require Import List.
Import ListNotations.
Require Import Lia.

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
  | sm_End   : forall (c : conf),
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
                      
  | sm_Add   : forall (q : prog) (x y : Z) (m : state Z)
                      (s i o : list Z) (c' : conf)
                      (EXEC : ((x + y)%Z::s, m, i, o) -- q --> c'),
      (y::x::s, m, i, o) -- (B Add)::q --> c'
                         
  | sm_Sub   : forall (q : prog) (x y : Z) (m : state Z)
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
  Proof. generalize st s i o n p c VAL EXEC. clear EXEC VAL c p n o i s st. induction e; intros.
    inversion VAL. apply sm_Const. exact EXEC.
    inversion VAL. apply sm_Load with n. exact VAR. exact EXEC.
      assert (forall b : bop, compile_expr (Bop b e1 e2) ++ p = compile_expr e1 ++ compile_expr e2 ++ [B b] ++ p).
        intro. simpl.
        rewrite <- (app_assoc (compile_expr e1) (compile_expr e2 ++ [B b0]) p).
        rewrite <- (app_assoc (compile_expr e2) ([B b0]) p). reflexivity.
    inversion VAL; subst.
      rewrite (H Add). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Add. exact EXEC.
      rewrite (H Sub). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Sub. exact EXEC.
      rewrite (H Mul). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Mul. exact EXEC.
      rewrite (H Div). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Div. exact NZERO. exact EXEC.
      rewrite (H Mod). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Mod. exact NZERO. exact EXEC.
      rewrite (H Le). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Le_T. exact OP. exact EXEC.
      rewrite (H Le). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Le_F. exact OP. exact EXEC.
      rewrite (H Lt). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Lt_T. exact OP. exact EXEC.
      rewrite (H Lt). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Lt_F. exact OP. exact EXEC.
      rewrite (H Ge). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Ge_T. exact OP. exact EXEC.
      rewrite (H Ge). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Ge_F. exact OP. exact EXEC.
      rewrite (H Gt). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Gt_T. exact OP. exact EXEC.
      rewrite (H Gt). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Gt_F. exact OP. exact EXEC.
      rewrite (H Eq). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Eq_T. exact OP. exact EXEC.
      rewrite (H Eq). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Eq_F. exact OP. exact EXEC.
      rewrite (H Ne). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Ne_T. exact OP. exact EXEC.
      rewrite (H Ne). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Ne_F. exact OP. exact EXEC.
      rewrite (H And). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_And. exact BOOLA. exact BOOLB. exact EXEC.
      rewrite (H Or). apply IHe1 with za. exact VALA. apply IHe2 with zb. exact VALB. apply sm_Or. exact BOOLA. exact BOOLB. exact EXEC.
  Qed.

  #[export] Hint Resolve compiled_expr_correct_cont.
  
  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof. rewrite -> (app_nil_end (compile_expr e)). apply compiled_expr_correct_cont with n. exact VAL. apply sm_End. Qed.
  
  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof. generalize st s i o p c EXEC. clear EXEC c p o i s st. induction e; intros.
    inversion EXEC. exists z. split. apply bs_Nat. exact EXEC0.
    inversion EXEC. exists z. split. apply bs_Var. exact VAR. exact EXEC0.
      assert (compile_expr (Bop b e1 e2) ++ p = compile_expr e1 ++ compile_expr e2 ++ [B b] ++ p).
        simpl. rewrite <- (app_assoc (compile_expr e1) (compile_expr e2 ++ [B b]) p).
        rewrite <- (app_assoc (compile_expr e2) ([B b]) p). reflexivity.
    rewrite -> H in EXEC. clear H.
      assert (exists x, [|e1|] st => x /\ (x :: s, st, i, o) -- compile_expr e2 ++ [B b] ++ p --> c).
        apply IHe1. exact EXEC.
    destruct H. destruct H.
      assert (exists y, [|e2|] st => y /\ (y :: x :: s, st, i, o) -- [B b] ++ p --> c).
        apply IHe2. exact H0.
    destruct H1. destruct H1.
    inversion H2; subst.
      exists (Z.add x x0). split. apply bs_Add. exact H. exact H1. exact EXEC0.
      exists (Z.sub x x0). split. apply bs_Sub. exact H. exact H1. exact EXEC0.
      exists (Z.mul x x0). split. apply bs_Mul. exact H. exact H1. exact EXEC0.
      exists (Z.div x x0). split. apply bs_Div. exact H. exact H1. exact NZERO. exact EXEC0.
      exists (Z.modulo x x0). split. apply bs_Mod. exact H. exact H1. exact NZERO. exact EXEC0.
      exists (Z.one). split. apply bs_Le_T with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.zero). split. apply bs_Le_F with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.one). split. apply bs_Ge_T with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.zero). split. apply bs_Ge_F with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.one). split. apply bs_Lt_T with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.zero). split. apply bs_Lt_F with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.one). split. apply bs_Gt_T with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.zero). split. apply bs_Gt_F with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.one). split. apply bs_Eq_T with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.zero). split. apply bs_Eq_F with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.one). split. apply bs_Ne_T with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.zero). split. apply bs_Ne_F with x x0. exact H. exact H1. exact OP. exact EXEC0.
      exists (Z.mul x x0). split. apply bs_And. exact H. exact H1. exact BOOLX. exact BOOLY. exact EXEC0.
      exists (zor x x0). split. apply bs_Or. exact H. exact H1. exact BOOLX. exact BOOLY. exact EXEC0.
  Qed.
  
  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof. rewrite -> (app_nil_end (compile_expr e)) in EXEC.
      assert (exists n0, [|e|] st => n0 /\ (n0 :: s, st, i, o) -- [] --> (n :: s, st, i, o)).
        apply compiled_expr_not_incorrect_cont. exact EXEC.
    destruct H. destruct H. inversion H0. subst. exact H.
  Qed.
  
  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof. split; intro.
    apply compiled_expr_not_incorrect with s i o. exact H.
    apply compiled_expr_correct. exact H.
  Qed.
  
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
        (i o i' o' : list Z)
        (H : (st, i, o) == p ==> (st', i', o')) (q : prog) (c : conf)
        (EXEC : ([], st', i', o') -- q --> c) :
    ([], st, i, o) -- (compile p Sp) ++ q --> c.
  Proof. generalize st st' i o i' o' H q c EXEC. clear EXEC c q H o' i' o i st' st. induction Sp; intros; simpl; inversion H; subst.
    rewrite <- (app_assoc (compile_expr e) ([S x]) q). simpl.
    apply compiled_expr_correct_cont with z. exact VAL. apply sm_Store. exact EXEC.
    apply sm_Read. apply sm_Store. exact EXEC.
    rewrite <- (app_assoc (compile_expr e) ([W]) q). simpl.
    apply compiled_expr_correct_cont with z. exact VAL.
    apply sm_Write. exact EXEC.
    exact EXEC.
    rewrite <- (app_assoc (compile s1 Sp1) (compile s2 Sp2) q).
    destruct c'. destruct p.
    assert (([], s, l0, l) -- compile s2 Sp2 ++ q --> c).
      apply IHSp2 with st' i' o'. exact STEP2. exact EXEC.
    assert (([], st, i, o) -- compile s1 Sp1 ++ compile s2 Sp2 ++ q --> c).
      apply IHSp1 with s l0 l. exact STEP1. exact H0.
    exact H1.
  Qed.
  
  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof. rewrite (app_nil_end (compile p Sp)). apply compiled_straightline_correct_cont with st' i' o'. exact EXEC. apply sm_End. Qed.
  
  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof. generalize st i o q c EXEC. clear EXEC c q o i st. induction Sp; intros.
    assert (exists n : Z, [|e|] st => n /\ ([n], st, i, o) -- [S x] ++ q --> c).
      apply compiled_expr_not_incorrect_cont. rewrite -> (app_assoc (compile_expr e) ([S x]) q). exact EXEC.
    destruct H. destruct H. inversion H0. subst.
    exists st [x <- x0], i, o. split. apply bs_Assign. exact H. exact EXEC0.
    replace (compile (READ x) (sl_Read x)) with [R; S x] in EXEC. replace ([R ; S x] ++ q) with (R :: (S x) :: q) in EXEC.
    inversion EXEC. subst. inversion EXEC0. subst.
    exists st [x <- z], i0, o. split. apply bs_Read. exact EXEC1. reflexivity. reflexivity.
    assert (exists n : Z, [|e|] st => n /\ ([n], st, i, o) -- [W] ++ q --> c).
      apply compiled_expr_not_incorrect_cont. rewrite -> (app_assoc (compile_expr e) ([W]) q). exact EXEC.
    destruct H. destruct H. inversion H0. subst.
    exists st, i, (x :: o). split. apply bs_Write. exact H. exact EXEC0.
    replace (compile SKIP sl_Skip) with ([] : list insn) in EXEC. replace ([] ++ q) with q in EXEC.
    exists st, i, o. split. apply bs_Skip. apply EXEC. reflexivity. reflexivity.
    assert (exists (st' : state Z) (i' o' : list Z), (st, i, o) == s1 ==> (st', i', o') /\ ([], st', i', o') -- compile s2 Sp2 ++ q --> c).
      apply IHSp1. rewrite -> (app_assoc (compile s1 Sp1) (compile s2 Sp2) q). exact EXEC.
    destruct H. destruct H. destruct H. destruct H.
    assert (exists (st' : state Z) (i' o' : list Z), (x, x0, x1) == s2 ==> (st', i', o') /\ ([], st', i', o') -- q --> c).
      apply IHSp2. exact H0.
    destruct H1. destruct H1. destruct H1. destruct H1.
    exists x2, x3, x4. split. apply bs_Seq with (x, x0, x1). exact H. exact H1. exact H2.
  Qed.
  
  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof.
    assert (exists (st_ : state Z) (i_ o_ : list Z), (st, i, o) == p ==> (st_, i_, o_) /\ ([], st_, i_, o_) -- [] --> ([], st', i', o')).
      apply compiled_straightline_not_incorrect_cont with Sp. rewrite <- (app_nil_end (compile p Sp)). exact EXEC.
    destruct H. destruct H. destruct H. destruct H. inversion H0. subst. exact H.
  Qed.
  
  Theorem straightline_compiler_correct
          (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z) :
    (st, i, o) == p ==> (st', i', o') <-> ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof. split.
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

Fixpoint label_occurs_ones_rec (occured : bool) (n: nat) (p : prog) : bool :=
  match p with
    LAB m :: p' => if eq_nat_dec n m
                   then if occured
                        then false
                        else label_occurs_ones_rec true n p'
                   else label_occurs_ones_rec occured n p'
  | _     :: p' => label_occurs_ones_rec occured n p'
  | []          => occured
  end.

Definition label_occurs_ones (n : nat) (p : prog) : bool := label_occurs_ones_rec false n p.

Fixpoint prog_wf_rec (prog p : prog) : bool :=
  match p with
    []      => true
  | i :: p' => match i with
                 JMP l => label_occurs_ones l prog
               | JZ  l => label_occurs_ones l prog
               | JNZ l => label_occurs_ones l prog
               | _     => true
               end && prog_wf_rec prog p'
                                  
  end.

Definition prog_wf (p : prog) : bool := prog_wf_rec p p.

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
                        (P p : prog)
                        (i   : StraightLine.insn)
                        (H   : c == [i] ==> c')
                        (HP  : P |- c' -- p --> c''), P |- c -- B i :: p --> c''
           
| sm_Label     : forall (c c' : conf)
                        (P p : prog)
                        (l : nat)
                        (H : P |- c -- p --> c'), P |- c -- LAB l :: p --> c'
                                                         
| sm_JMP       : forall (c c' : conf)
                        (P p : prog)
                        (l : nat)
                        (H : P |- c -- at_label l P --> c'), P |- c -- JMP l :: p --> c'
                                                                    
| sm_JZ_False  : forall (s i o : list Z)
                        (m : state Z)
                        (c' : conf)
                        (P p : prog)
                        (l : nat)
                        (z : Z)
                        (HZ : z <> 0%Z)
                        (H : P |- (s, m, i, o) -- p --> c'), P |- (z :: s, m, i, o) -- JZ l :: p --> c'
                                                                                    
| sm_JZ_True   : forall (s i o : list Z)
                        (m : state Z)
                        (c' : conf)
                        (P p : prog)
                        (l : nat)
                        (H : P |- (s, m, i, o) -- at_label l P --> c'), P |- (0%Z :: s, m, i, o) -- JZ l :: p --> c'
                                                                                                 
| sm_JNZ_False : forall (s i o : list Z)
                        (m : state Z)
                        (c' : conf)
                        (P p : prog)
                        (l : nat)
                        (H : P |- (s, m, i, o) -- p --> c'), P |- (0%Z :: s, m, i, o) -- JNZ l :: p --> c'
                                                                                      
| sm_JNZ_True  : forall (s i o : list Z)
                        (m : state Z)
                        (c' : conf)
                        (P p : prog)
                        (l : nat)
                        (z : Z)
                        (HZ : z <> 0%Z)
                        (H : P |- (s, m, i, o) -- at_label l P --> c'), P |- (z :: s, m, i, o) -- JNZ l :: p --> c'
| sm_Empty : forall (c : conf) (P : prog), P |- c -- [] --> c 
where "P '|-' c1 '--' q '-->' c2" := (sm_int P c1 q c2).
