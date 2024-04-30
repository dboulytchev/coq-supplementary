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
    revert VAL EXEC. revert n. revert s. revert p. induction e; intros.
    - simpl. 
      assert ([|Nat z|] st => (z)). {auto. }
      remember (eval_deterministic (Nat z) st n z VAL H).
      subst z. 
      apply sm_Const. assumption.
    - eapply sm_Load with (z := n).
      + inversion VAL. assumption.
      + assumption.
    - simpl.
      inversion VAL;
        rewrite <- app_assoc;
        rewrite <- app_assoc;
        apply (IHe1) with (n := za); auto;
        apply (IHe2) with (n := zb); auto.
        + apply sm_Add. assumption. rewrite -> H4. assumption. 
        + apply sm_Sub. assumption. rewrite -> H4. assumption. 
        + apply sm_Mul. rewrite -> H4. assumption. 
        + apply sm_Div. assumption. rewrite -> H4. assumption. 
        + apply sm_Mod. assumption. rewrite -> H4. assumption. 
        + apply sm_Le_T. assumption. rewrite -> H4. assumption. 
        + apply sm_Le_F. assumption. rewrite -> H4. assumption.
        + apply sm_Lt_T. assumption. rewrite -> H4. assumption. 
        + apply sm_Lt_F. assumption. rewrite -> H4. assumption.
        + apply sm_Ge_T. assumption. rewrite -> H4. assumption. 
        + apply sm_Ge_F. assumption. rewrite -> H4. assumption.
        + apply sm_Gt_T. assumption. rewrite -> H4. assumption. 
        + apply sm_Gt_F. assumption. rewrite -> H4. assumption.
        + apply sm_Eq_T. assumption. rewrite -> H4. assumption. 
        + apply sm_Eq_F. assumption. rewrite -> H4. assumption.
        + apply sm_Ne_T. assumption. rewrite -> H4. assumption. 
        + apply sm_Ne_F. assumption. rewrite -> H4. assumption.
        + apply sm_And. assumption. assumption.
          rewrite -> H4. assumption.
        + apply sm_Or. assumption. assumption.
          rewrite -> H4. assumption.
  Qed.

  #[export] Hint Resolve compiled_expr_correct_cont.
  
  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof.
    remember (@nil insn) as p.
    remember ((n :: s, st, i, o)) as c.
    assert (c -- p --> c). {
      rewrite -> Heqp.
      apply sm_End.
      assumption.
    } 
    remember (compiled_expr_correct_cont e st s i o n p c VAL).  
    assert (((n :: s, st, i, o)) -- [] --> (c)).
    { subst c. subst p. assumption. }
    assert (compile_expr e ++ p = compile_expr e). {
      assert (forall (l : list insn),
      l ++ nil = l). 
      {
          intros. induction l.
          - reflexivity.
          - simpl. rewrite -> IHl. reflexivity.  
      }
      subst p. apply ( H1 (compile_expr e)).
    }
    rewrite <- H1.
    eapply compiled_expr_correct_cont.
    eassumption.
    subst p. assumption.
  Qed.
  
  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof.
    revert EXEC. revert p. revert s. induction e; intros.
    - simpl in EXEC.
      econstructor. split.
      + apply (bs_Nat).
      + inversion EXEC. assumption.
    - simpl in EXEC.
      inversion EXEC.
      econstructor. split.
      + constructor. eassumption.
      + assumption.
    - simpl in EXEC.
      rewrite <- app_assoc in EXEC.
      rewrite <- app_assoc in EXEC.
      specialize (IHe1 s (compile_expr e2 ++ [B b] ++ p) EXEC).
      destruct IHe1. destruct H. 
      specialize (IHe2 (x :: s) ([B b] ++ p) H0).
      destruct IHe2. destruct H1. 
      simpl in H2. 
      destruct b.
      + inversion H2. econstructor. split.
        apply bs_Add. eassumption. eassumption.
        assumption.
      + inversion H2. econstructor. split.
        apply bs_Sub. eassumption. eassumption.
        assumption.
      + inversion H2. econstructor. split.
        apply bs_Mul. eassumption. eassumption.
        assumption.
      + inversion H2. econstructor. split.
        apply bs_Div. eassumption. eassumption.
        assumption. assumption.
      + inversion H2. econstructor. split.
        apply bs_Mod. eassumption. eassumption.
        assumption. assumption.
      + inversion H2. 
        * econstructor. split.
          eapply bs_Le_T. eassumption. eassumption.
          assumption. assumption.
        * econstructor. split. 
          eapply bs_Le_F. eassumption. eassumption.
          assumption. assumption.
      + inversion H2. 
        * econstructor. split.
          eapply bs_Lt_T. eassumption. eassumption.
          assumption. assumption.
        * econstructor. split. 
          eapply bs_Lt_F. eassumption. eassumption.
          assumption. assumption.
      + inversion H2. 
        * econstructor. split.
          eapply bs_Ge_T. eassumption. eassumption.
          assumption. assumption.
        * econstructor. split. 
          eapply bs_Ge_F. eassumption. eassumption.
          assumption. assumption.
      + inversion H2. 
        * econstructor. split.
          eapply bs_Gt_T. eassumption. eassumption.
          assumption. assumption.
        * econstructor. split. 
          eapply bs_Gt_F. eassumption. eassumption.
          assumption. assumption.
      + inversion H2. 
        * econstructor. split.
          eapply bs_Eq_T. eassumption. eassumption.
          assumption. assumption.
        * econstructor. split. 
          eapply bs_Eq_F. eassumption. eassumption.
          assumption. assumption.
      + inversion H2. 
        * econstructor. split.
          eapply bs_Ne_T. eassumption. eassumption.
          assumption. assumption.
        * econstructor. split. 
          eapply bs_Ne_F. eassumption. eassumption.
          assumption. assumption.
      + inversion H2. econstructor. split.
        apply bs_And. eassumption. eassumption.
        assumption. assumption.
        assumption.
      + inversion H2. econstructor. split.
        apply bs_Or. eassumption. eassumption.
        assumption. assumption.
        assumption.
  Qed.
    
  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof.
    remember (@nil insn) as p.
    remember ((n :: s, st, i, o)) as c.
    assert (c -- p --> c). {
      rewrite -> Heqp.
      apply sm_End.
      assumption.
    } 
    remember (compiled_expr_not_incorrect_cont e st s i o p c).  
    assert (compile_expr e ++ p = compile_expr e). {
      assert (forall (l : list insn),
      l ++ nil = l). 
      {
          intros. induction l.
          - reflexivity.
          - simpl. rewrite -> IHl. reflexivity.  
      }
      subst p. apply ( H0 (compile_expr e)).
    }
    rewrite <- H0 in EXEC.
    remember (e0 EXEC).
    destruct e1. destruct a.
    subst c. subst p. 
    inversion s0.
    subst x. assumption.
  Qed.

  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof.
    split. 
    - apply compiled_expr_not_incorrect.
    - apply compiled_expr_correct.
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
        (s i o s' i' o' : list Z)
        (H : (st, i, o) == p ==> (st', i', o')) (q : prog) (c : conf)
        (EXEC : ([], st', i', o') -- q --> c) :
    ([], st, i, o) -- (compile p Sp) ++ q --> c.
  Proof.
    revert H EXEC. revert q st st' i o i' o'. induction Sp; intros; simpl.
    - rewrite <- app_assoc.
      inversion H. 
      eapply (compiled_expr_correct_cont). eassumption.
      simpl. apply sm_Store. subst st'.
      assumption.
    - inversion H. subst i. apply sm_Read.
      apply sm_Store. subst st'. assumption.
    - rewrite <- app_assoc.
      inversion H.
      eapply compiled_expr_correct_cont. eassumption.
      apply sm_Write. subst o'. assumption.
    - inversion H. assumption.
    - rewrite <- app_assoc.
      inversion H. destruct c'. destruct p.
      apply (IHSp1 (compile s2 Sp2 ++ q) st s4 i o l0 l). assumption.
      apply (IHSp2 q s4 st' l0 l i' o'). assumption.
      assumption.
  Qed.

  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    remember (@nil insn) as q.
    remember ((@nil Z, st', i, o)) as c.

    assert (compile p Sp ++ q = compile p Sp). {
      assert (forall (l : list insn),
      l ++ nil = l). 
      {
          intros. induction l.
          - reflexivity.
          - simpl. rewrite -> IHl. reflexivity.  
      }
      subst q. apply H.
    }
    rewrite <- H.
    remember (compiled_straightline_correct_cont p Sp st st' nil i o nil i' o' EXEC q (([], st', i', o'))).
    assert ((([], st', i', o')) -- q --> (([], st', i', o'))). {
      rewrite -> Heqq.
      apply (sm_End nil).
    } 
    apply (s H0).
  Qed.

  
  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof. 
    revert EXEC. revert q. revert i o st c. induction Sp; intros; simpl in EXEC.
    - rewrite <- app_assoc in EXEC.
      remember (compiled_expr_not_incorrect_cont e st nil i o ([S x] ++ q) c EXEC).
      inversion e0. destruct H.
      inversion H0.
      econstructor. econstructor. econstructor.
      split. apply bs_Assign. eassumption. assumption.
    - inversion EXEC. inversion EXEC0.
      repeat econstructor. assumption.
    - rewrite <- app_assoc in EXEC.
      remember (compiled_expr_not_incorrect_cont e st nil i o ([W] ++ q) c EXEC).
      inversion e0. destruct H.
      repeat econstructor.
      eassumption.
      inversion H0. assumption.
    - repeat econstructor. assumption.
    - rewrite <- app_assoc in EXEC.
      specialize (IHSp1 i o st c (compile s2 Sp2 ++ q) EXEC).
      inversion IHSp1. inversion H. inversion H0. inversion H1.
      specialize (IHSp2 x0 x1 x c q H3).
      inversion IHSp2. inversion H4. inversion H5. inversion H6.
      repeat econstructor. eassumption.
      eassumption. assumption.
  Qed.

  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof.
    remember (@nil insn) as q.
    remember ((@nil Z, st', i, o)) as c.



    assert (compile p Sp ++ q = compile p Sp). {
      assert (forall (l : list insn),
      l ++ nil = l). 
      {
          intros. induction l.
          - reflexivity.
          - simpl. rewrite -> IHl. reflexivity.  
      }
      subst q. apply H.
    }
    rewrite <- H in EXEC.
    remember (compiled_straightline_not_incorrect_cont p Sp st i o q (([], st', i', o')) EXEC).
    destruct e. destruct e. destruct e. destruct a.
    subst q. inversion s. subst c0. subst x. subst x0. subst x1.
    assumption.
  Qed.
  
  Theorem straightline_compiler_correct
          (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z) :
    (st, i, o) == p ==> (st', i', o') <-> ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    split.
    - apply compiled_straightline_correct.
    - apply compiled_straightline_not_incorrect.
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
  { simpl. rewrite Hocc. auto. }
  { simpl in Hwf. destruct a; simpl; apply Bool.andb_true_iff in Hwf; inversion Hwf; intuition.
  }
Qed.

Lemma wf_rev (p q : prog) (Hwf : prog_wf_rec q p = true) : prog_wf_rec q (rev p) = true.
Proof. admit. Admitted.

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
