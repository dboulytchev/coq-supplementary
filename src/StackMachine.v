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
    generalize dependent c.
    generalize dependent s.
    generalize dependent p.
    generalize dependent n.
    induction e; intros.
    - simpl. econstructor. inversion_clear VAL. assumption.
    - simpl. econstructor.
      + inversion_clear VAL. apply VAR.
      + assumption.
    - simpl. inversion VAL; subst; rewrite <- app_assoc; rewrite <- app_assoc.
      all: eapply IHe1; try (apply VALA); eapply IHe2; try (apply VALB); econstructor; assumption.
  Qed.
  
  Hint Resolve compiled_expr_correct_cont.
  
  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof.
    induction e; intros.
    - simpl. econstructor. inversion_clear VAL. econstructor. exact [].
    - simpl. econstructor. inversion_clear VAL.
      + apply VAR.
      + econstructor. exact [].
    - simpl.
      inversion VAL; subst; simpl.
      all: apply compiled_expr_correct_cont with (n := za); auto.
      all: apply compiled_expr_correct_cont with (n := zb); auto.
      all: try (econstructor; try econstructor; auto; exact []).
      all: econstructor; auto; econstructor; exact [].
  Qed.
  
  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof.
    generalize dependent p.
    generalize dependent s.
    induction e; intros.
    - inversion_clear EXEC. exists z. split; auto.
    - inversion_clear EXEC. exists z. split; auto.
    - simpl in EXEC. rewrite <- app_assoc in EXEC. rewrite <- app_assoc in EXEC.
      specialize (IHe1 s (compile_expr e2 ++ [B b] ++ p) EXEC).
      destruct IHe1 as [z1 H1]. destruct H1 as [H1l H1r].
      specialize (IHe2 (z1 :: s) ([B b] ++ p) H1r).
      destruct IHe2 as [z2 H2]. destruct H2 as [H2l H2r].
      simpl in H2r. eauto. inversion H2r; subst.
      all: try (exists Z.one; split; auto; econstructor; try (apply H1l); try (apply H2l); assumption).
      all: try (exists Z.zero; split; auto; econstructor; try (apply H1l); try (apply H2l); assumption).
      + exists (z1 + z2)%Z. split; auto.
      + exists (z1 - z2)%Z. split; auto.
      + exists (z1 * z2)%Z. split; auto.
      + exists (Z.div z1 z2). split; auto.
      + exists (Z.modulo z1 z2). split; auto.
      + exists (z1 * z2)%Z. split; auto. 
      + exists (zor z1 z2). split; auto.
  Qed.

  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof.
    generalize dependent n.
    induction e; intros.
    - inversion EXEC. inversion EXEC0. subst. auto.
    - inversion EXEC. inversion EXEC0. subst. econstructor. auto.
    - simpl in EXEC.
      remember (compiled_expr_not_incorrect_cont e1 st s i o (compile_expr e2 ++ [B b]) (n :: s, st, i, o) EXEC) as P.
      destruct P as [z1 P1]. destruct P1 as [P1l P1r].
      remember (compiled_expr_not_incorrect_cont e2 st (z1 :: s) i o ([B b]) (n :: s, st, i, o) P1r) as P.
      destruct P as [z2 P2]. destruct P2 as [P2l P2r].
      clear HeqP HeqP0.
      destruct b.
      all: (inversion P2r; inversion EXEC0; subst; econstructor; eauto).
  Qed.

  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof.
    split; intro H.
    - eapply compiled_expr_not_incorrect; eauto.
    - eapply compiled_expr_correct. assumption.
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
    generalize dependent c.
    generalize dependent st'.
    generalize dependent i'.
    generalize dependent o'.
    generalize dependent st.
    generalize dependent i.
    generalize dependent o.
    induction Sp; intros; simpl.
    - rewrite <- app_assoc. simpl.
      inversion H. subst.
      eapply compiled_expr_correct_cont; eauto.
      econstructor. assumption.
    - inversion H. subst.
      econstructor. econstructor. assumption.
    - rewrite <- app_assoc. simpl.
      inversion H. subst.
      eapply compiled_expr_correct_cont; eauto.
      econstructor. assumption.
    - inversion_clear H. assumption.
    - rewrite <- app_assoc.
      inversion_clear H.
      destruct c' as [[st'' i''] o''].
      eauto.
  Qed.
  
  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof. 
    generalize dependent st.
    generalize dependent i.
    generalize dependent o.
    induction Sp; simpl; intros.
    - inversion_clear EXEC. 
      eapply compiled_expr_correct_cont; eauto.
      econstructor. econstructor. exact [].
    - inversion_clear EXEC. 
      econstructor. econstructor. econstructor. exact [].
    - inversion_clear EXEC.
      eapply compiled_expr_correct_cont; eauto.
      econstructor. econstructor. exact [].
    - inversion_clear EXEC. econstructor. exact [].
    - inversion_clear EXEC. destruct c' as [[st'' i''] o'']. 
      eapply compiled_straightline_correct_cont; eauto.
  Qed.

  Ltac eexists3 :=
    eexists; eexists; eexists.

  Ltac e3_cons_inv :=
    eexists3; split; 
    try (econstructor; eauto);
    try assumption; try (inversion_clear CONT); assumption.
  
  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof.
    generalize dependent st.
    generalize dependent i.
    generalize dependent o.
    generalize dependent q.
    induction Sp; intros; simpl in EXEC.
    all: try (rewrite <- app_assoc in EXEC); simpl in EXEC.
    - eapply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [n [VAL CONT]].
      e3_cons_inv.
    - inversion_clear EXEC. inversion_clear EXEC0.
      e3_cons_inv.
    - eapply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [n [VAL CONT]].
      e3_cons_inv.
    - e3_cons_inv.
    - specialize (IHSp1 (compile s2 Sp2 ++ q) o i st EXEC).
      destruct IHSp1 as [st'' [i'' [o'' [STEP CONT]]]].
      specialize (IHSp2 q o'' i'' st'' CONT).
      destruct IHSp2 as [st_f [i_f [o_f [STEP2 CONT2]]]].
      eexists3. split; eauto.
      econstructor; eauto.
  Qed.
  
  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof.
    generalize dependent o.
    generalize dependent i.
    generalize dependent st.
    induction Sp; intros; simpl in EXEC.
    - eapply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [n [VAL CONT]].
      inversion CONT. inversion EXEC. subst.
      econstructor. assumption.
    - inversion EXEC. inversion EXEC0. inversion EXEC1. subst.
      econstructor.
    - eapply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [n [VAL CONT]].
      inversion CONT. inversion EXEC. subst.
      econstructor. assumption.
    - inversion_clear EXEC. econstructor.
    - remember (compiled_straightline_not_incorrect_cont s1 Sp1 st i o (compile s2 Sp2) ([], st', i', o') EXEC) as P.
      destruct P as [st'' [i'' [o'' [STEP CONT]]]].
      clear HeqP.
      econstructor; eauto.
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

