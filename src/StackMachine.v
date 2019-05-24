Require Import List.
Import ListNotations.
Require Import Omega.

From Bignums Require Export BigZ.
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
  Inductive insn : Type :=
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
    generalize dependent o.
    generalize dependent i.
    generalize dependent s.
    generalize dependent p.
    
    induction VAL; intros p s' i' o' EXEC; simpl.
    (*3-7, 20-21 :*)
    1 : { apply sm_Const. assumption. }
    1 : { apply sm_Load with (z). assumption. assumption. }
    all : rewrite <- app_assoc; rewrite <- app_assoc;
      apply IHVAL1; apply IHVAL2; simpl; [> apply sm_Add |
                                            apply sm_Sub |
                                            apply sm_Mul |
                                            apply sm_Div |
                                            apply sm_Mod |
                                            apply sm_Le_T |
                                            apply sm_Le_F |
                                            apply sm_Lt_T |
                                            apply sm_Lt_F |
                                            apply sm_Ge_T |
                                            apply sm_Ge_F |
                                            apply sm_Gt_T |
                                            apply sm_Gt_F |
                                            apply sm_Eq_T |
                                            apply sm_Eq_F |
                                            apply sm_Ne_T |
                                            apply sm_Ne_F |
                                            apply sm_And |
                                            apply sm_Or]; assumption.
  Qed.

  Hint Resolve compiled_expr_correct_cont.
  
  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof.
    induction VAL.
    1 : { apply sm_Const. apply sm_End. apply []. }
    1 : { simpl. apply sm_Load with (z). assumption.  
      apply sm_End. apply [].
    }
    all : simpl; apply compiled_expr_correct_cont with (za); try assumption;
      apply compiled_expr_correct_cont with (zb); try assumption; 
      [> apply sm_Add |
         apply sm_Sub |
         apply sm_Mul |
         apply sm_Div |
         apply sm_Mod |
         apply sm_Le_T |
         apply sm_Le_F |
         apply sm_Lt_T |
         apply sm_Lt_F |
         apply sm_Ge_T |
         apply sm_Ge_F |
         apply sm_Gt_T |
         apply sm_Gt_F |
         apply sm_Eq_T |
         apply sm_Eq_F |
         apply sm_Ne_T |
         apply sm_Ne_F |
         apply sm_And |
         apply sm_Or];
      try assumption; try apply sm_End; try apply [].
  Qed.

  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof.
    generalize dependent c.
    generalize dependent p.
    generalize dependent o.
    generalize dependent i.
    generalize dependent s.
    generalize dependent st.
    induction e; intros st s i' o' p c EXEC.
    - exists z. split. apply bs_Nat.
      simpl in EXEC. inversion EXEC. assumption.
    - simpl in EXEC. inversion EXEC. subst. exists z.
      split. apply bs_Var. assumption. assumption.
    - simpl in EXEC. rewrite <- app_assoc in EXEC. rewrite <- app_assoc in EXEC.
      apply IHe1 in EXEC. destruct EXEC as [z1 [VAL1 EXEC2]].
      apply IHe2 in EXEC2. destruct EXEC2 as [z2 [VAL2 EXEC_BOP]].
      simpl in EXEC_BOP. inversion EXEC_BOP; subst;
      [> exists (z1 + z2)%Z
       | exists (z1 - z2)%Z
       | exists (z1 * z2)%Z
       | exists (Z.div z1 z2)
       | exists (Z.modulo z1 z2)
       | exists Z.one
       | exists Z.zero
       | exists Z.one
       | exists Z.zero
       | exists Z.one
       | exists Z.zero
       | exists Z.one
       | exists Z.zero
       | exists Z.one
       | exists Z.zero
       | exists Z.one
       | exists Z.zero
       | exists (z1 * z2)%Z
       | exists (zor z1 z2)
      ]; split; try assumption;
      [> apply bs_Add |
         apply bs_Sub |
         apply bs_Mul |
         apply bs_Div |
         apply bs_Mod |
         apply bs_Le_T with (z1) (z2) |
         apply bs_Le_F with (z1) (z2) |
         apply bs_Ge_T with (z1) (z2) |
         apply bs_Ge_F with (z1) (z2) |
         apply bs_Lt_T with (z1) (z2) |
         apply bs_Lt_F with (z1) (z2) |
         apply bs_Gt_T with (z1) (z2) |
         apply bs_Gt_F with (z1) (z2) |
         apply bs_Eq_T with (z1) (z2) |
         apply bs_Eq_F with (z1) (z2) |
         apply bs_Ne_T with (z1) (z2) |
         apply bs_Ne_F with (z1) (z2) |
         apply bs_And |
         apply bs_Or]; assumption.
  Qed.

  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof.
    destruct e.
    - inversion EXEC. inversion EXEC0. apply bs_Nat.
    - inversion EXEC. inversion EXEC0. 
      subst. apply bs_Var. assumption.
    - destruct b; simpl in EXEC; 
      apply compiled_expr_not_incorrect_cont in EXEC;
      destruct EXEC as [z1 [VAL1 EXEC2]];
      apply compiled_expr_not_incorrect_cont in EXEC2;
      destruct EXEC2 as [z2 [VAL2 EXEC0]];
      inversion EXEC0; inversion EXEC;
      [> apply bs_Add |
         apply bs_Sub |
         apply bs_Mul |
         apply bs_Div |
         apply bs_Mod |
         apply bs_Le_T with (z1) (z2) |
         apply bs_Le_F with (z1) (z2) |
         apply bs_Lt_T with (z1) (z2) |
         apply bs_Lt_F with (z1) (z2) |
         apply bs_Ge_T with (z1) (z2) |
         apply bs_Ge_F with (z1) (z2) |
         apply bs_Gt_T with (z1) (z2) |
         apply bs_Gt_F with (z1) (z2) |
         apply bs_Eq_T with (z1) (z2) |
         apply bs_Eq_F with (z1) (z2) |
         apply bs_Ne_T with (z1) (z2) |
         apply bs_Ne_F with (z1) (z2) |
         apply bs_And |
         apply bs_Or]; assumption.
  Qed.

  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof.
    split; intros H.
    - apply compiled_expr_not_incorrect in H. assumption.
    - apply compiled_expr_correct. assumption.
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
    generalize dependent q.
    generalize dependent o'.
    generalize dependent i'.
    generalize dependent st'.
    generalize dependent o.
    generalize dependent i.
    generalize dependent st.
    induction Sp; intros st i o st' i' o' BS_EXEC q EXEC; simpl; inversion BS_EXEC.
    - rewrite <- app_assoc.
      apply compiled_expr_correct_cont with (n:=z). assumption.
      simpl. apply sm_Store. subst. assumption.
    - apply sm_Read. apply sm_Store. subst. assumption.
    - rewrite <- app_assoc.
      apply compiled_expr_correct_cont with (n:=z). assumption.
      simpl. apply sm_Write. subst. assumption.
    - assumption.
    - destruct c' as [[st'' i''] o''].
      rewrite <- app_assoc.
      apply IHSp1 with (st':=st'') (i':=i'') (o':=o''). assumption.
      apply IHSp2 with (st':=st') (i':=i') (o':=o'). assumption.
      assumption.
  Qed.
  
  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    generalize dependent o.
    generalize dependent i.
    generalize dependent st.
    induction Sp; intros st i o EXEC; simpl; inversion EXEC.
    - apply compiled_expr_correct_cont with (n:=z). assumption.
      apply sm_Store. apply sm_End. apply [].
    - apply sm_Read. apply sm_Store. apply sm_End. apply [].
    - apply compiled_expr_correct_cont with (n:=z). assumption.
      apply sm_Write. apply sm_End. apply [].
    - apply sm_End. apply [].
    - simpl. inversion EXEC. destruct c' as [[st'' i''] o''].
      apply compiled_straightline_correct_cont with (st'') (i'') (o'');
      try assumption. apply IHSp2. assumption.
  Qed.

  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof.
    generalize dependent q.
    generalize dependent o.
    generalize dependent i.
    generalize dependent st.
    induction Sp; intros st i o q EXEC; simpl in EXEC.
    - rewrite <- app_assoc in EXEC.
      apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [n [VAL EXEC0]].
      exists st[x <- n]. exists i. exists o.
      split.
      + apply bs_Assign. assumption.
      + simpl in EXEC0. inversion EXEC0. assumption.
    - inversion EXEC. inversion EXEC0.
      exists st[x <- z]. exists i0. exists o.
      split.
      + apply bs_Read.
      + assumption.
    - rewrite <- app_assoc in EXEC.
      apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [n [VAL EXEC0]].
      simpl in EXEC0. inversion EXEC0.
      exists st. exists i. exists (n :: o).
      split.
      + apply bs_Write. assumption.
      + assumption.
    - exists st. exists i. exists o.
      split.
      + apply bs_Skip.
      + assumption.
    - rewrite <- app_assoc in EXEC. apply IHSp1 in EXEC.
      destruct EXEC as [st' [i' [o' [EXEC1_BS EXEC2]]]].
      apply IHSp2 in EXEC2.
      destruct EXEC2 as [st'' [i'' [o'' [EXEC2_BS EXEC_q]]]].
      exists st''. exists i''. exists o''.
      split.
      + apply bs_Seq with ((st', i', o')). assumption. assumption.
      + assumption.
  Qed.
      
  
  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof.
    generalize dependent o.
    generalize dependent i.
    generalize dependent st.
    induction Sp; intros st i o EXEC; simpl in EXEC.
    - apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [n [VAL EXEC0]].
      inversion EXEC0. inversion EXEC. subst.
      apply bs_Assign. assumption.
    - inversion EXEC. inversion EXEC0. inversion EXEC1.
      apply bs_Read.
    - apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [n [VAL EXEC0]].
      inversion EXEC0. inversion EXEC.
      apply bs_Write. subst. assumption.
    - inversion EXEC. subst. apply bs_Skip.
    - apply compiled_straightline_not_incorrect_cont in EXEC.
      destruct EXEC as [st'' [i'' [o'' [EXEC1_BS EXEC2]]]].
      apply IHSp2 in EXEC2. seq_apply.
  Qed.
  
  Theorem straightline_compiler_correct
          (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z) :
    (st, i, o) == p ==> (st', i', o') <-> ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    split; intros H.
    - apply compiled_straightline_correct. assumption.
    - apply compiled_straightline_not_incorrect in H. assumption.
  Qed.

End StraightLine.

