Require Import BinInt ZArith_dec.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Export Id.
Require Export State.
Require Export Expr.
Require Export Stmt.
Require Import Coq.Program.Equality.

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

  Lemma sm_int_assoc (c c1 c2 : conf) (p1 p2 : prog)
        (H1: c -- p1 --> c1)
        (H2: c1 -- p2 --> c2) :
        (c -- p1 ++ p2 --> c2).
  Proof.
    generalize dependent p2.
    generalize dependent c2.
    generalize dependent c.
    generalize dependent c1.
    induction p1; intros; simpl; inversion H1;
    try assumption;
    solve [econstructor; try eassumption; eapply IHp1; eassumption].
  Qed.

  Lemma sm_int_assoc_inv (c c2 : conf) (p1 p2 : prog)
        (H: c -- p1 ++ p2 --> c2) : exists c1,
        (c -- p1 --> c1) /\ (c1 -- p2 --> c2). 
  Proof.
    generalize dependent c.
    induction p1; intros.
    - exists c. split.
      * constructor. assumption.
      * assumption.
    - inversion H;
      apply IHp1 in EXEC; destruct EXEC as [c1 []]; exists c1; split;
      try assumption;
      try solve [econstructor; try eassumption].
  Qed.

  Lemma sm_int_deterministic (c c1 c2 : conf) (p : prog)
        (H1: c -- p --> c1)
        (H2: c -- p --> c2) :
        c1 = c2.
  Proof.
    generalize dependent c2.
    induction H1; intros; inversion H2; try reflexivity;
    subst;
    try congruence;
    apply IHsm_int; try assumption.
    replace z with z0.
    - assumption.
    - eapply state_deterministic; eassumption.
  Qed.
  
  (* Partial correctness of expression compiler *)
  Lemma compiled_expr_correct_cont
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (p : prog) (c : conf)
        (VAL : [| e |] st => n)
        (EXEC: (n::s, st, i, o) -- p --> c) :        
    (s, st, i, o) -- (compile_expr e) ++ p --> c.
  Proof.
    dependent induction e; inversion VAL; subst; simpl;
    try solve [ econstructor; eassumption ];
    rewrite <- app_assoc; eapply IHe1; try eassumption;
    rewrite <- app_assoc; eapply IHe2; try eassumption; 
    econstructor; eassumption.
  Qed.

  #[export] Hint Resolve compiled_expr_correct_cont.
  
  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof.
    induction e.
    - remember (compile_expr _) as l. rewrite Heql. constructor. inversion VAL. constructor. assumption.
    - remember (compile_expr _) as l. rewrite Heql. econstructor. 
      * inversion VAL. eassumption. 
      * constructor. assumption.
    - remember (compile_expr _) as l. rewrite Heql in *. destruct b; simpl; inversion VAL; 
      eapply compiled_expr_correct_cont; try eassumption;
      eapply compiled_expr_correct_cont; try eassumption;
      constructor; try assumption; constructor; assumption.
  Qed.
  
  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof. 
    dependent induction e.
    - eexists. split. 
      * econstructor.
      * inversion EXEC. assumption.
    - inversion EXEC.
      eexists. split.
      * econstructor. eassumption.
      * assumption.
    - simpl in EXEC. 
      rewrite <- app_assoc in EXEC. apply IHe1 in EXEC. destruct EXEC as [n1 [VAL1 EXEC]].
      rewrite <- app_assoc in EXEC. apply IHe2 in EXEC. destruct EXEC as [n2 [VAL2 EXEC]].
      inversion EXEC; subst; eexists; split; try eassumption; econstructor; eassumption.
  Qed.

  Lemma compiled_expr_not_nil (e: expr) (H: compile_expr e = []) : False.
  Proof.
    destruct e; simpl in *; try discriminate.
    match type of H with (?lhs = ?rhs) => assert (H1:length lhs = length rhs) end.
    * rewrite H. reflexivity.
    * simpl in H1. rewrite app_assoc in H1. rewrite last_length in H1. discriminate.
  Qed.

  Lemma sm_int_expr_not_nil e l st i o l' st' i' o'
    (H: (l, st, i, o) -- (compile_expr e) --> (l', st', i', o')) :
    exists z, l' = z::l.
  Proof.
    destruct e.
    - inversion H. inversion EXEC. subst. exists z. reflexivity.
    - inversion H. inversion EXEC. subst. exists z. reflexivity.
    - simpl in H. apply compiled_expr_not_incorrect_cont in H. destruct H as [n1 [H1 H2]].
      apply compiled_expr_not_incorrect_cont in H2. destruct H2 as [n2 [H2 H3]].
      inversion H3; inversion EXEC; subst; eexists; reflexivity.
  Qed.

  Lemma sm_int_expr_same e l st i o l' st' i' o'
    (H: (l, st, i, o) -- (compile_expr e) --> (l', st', i', o')) :
    (st, i, o) = (st', i', o').
  Proof.
    destruct e.
    - inversion H. inversion EXEC. auto.
    - inversion H. inversion EXEC. auto.
    - simpl in H. apply compiled_expr_not_incorrect_cont in H. destruct H as [n1 [H1 H2]].
      apply compiled_expr_not_incorrect_cont in H2. destruct H2 as [n2 [H2 H3]].
      inversion H3; inversion EXEC; auto.
  Qed.
  
  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof. 
    generalize dependent n.
    generalize dependent s.
    induction e; intros.
    - inversion EXEC. inversion EXEC0. constructor.
    - inversion EXEC. inversion EXEC0. subst. constructor. assumption.
    - apply sm_int_assoc_inv in EXEC. destruct EXEC as [[[[s1]]] [H1 EXEC]].
      destruct s1. { apply sm_int_expr_not_nil in H1. destruct H1. discriminate. }
      assert (E1: (s0, l, l0) = (st, i, o)). { symmetry. eapply sm_int_expr_same. eassumption. }
      assert (s1 = s). 
      { apply sm_int_expr_not_nil in H1. destruct H1 as [x1 H1]. injection H1; intros. assumption. }
      injection E1; intros; subst.
      apply sm_int_assoc_inv in EXEC. destruct EXEC as [[[[s2]]] [H2 EXEC]].
      destruct s2. { apply sm_int_expr_not_nil in H2. destruct H2. discriminate. }
      assert (E2: (s0, l, l0) = (st, i, o)). { symmetry. eapply sm_int_expr_same. eassumption. }
      assert (s2 = (z::s)). 
      { apply sm_int_expr_not_nil in H2. destruct H2 as [x2 H2]. injection H2; intros. assumption. }
      injection E2; intros; subst.
      apply IHe1 in H1.
      apply IHe2 in H2.
      inversion EXEC; inversion EXEC0; subst; econstructor; eassumption.
  Qed.
  
  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof.
    split. 
    - apply compiled_expr_not_incorrect.
    - remember ([R]) as p. 
      intros H. induction H.
      1: simpl. constructor. constructor. assumption.
      1: simpl. econstructor; try eassumption. constructor. assumption.
      all: simpl; 
        eapply compiled_expr_correct_cont; try eassumption;
        eapply compiled_expr_correct_cont; try eassumption.
      all: try solve [repeat (econstructor; try eassumption)].
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
    dependent induction Sp.
    - simpl. rewrite <- app_assoc. inversion H. eapply compiled_expr_correct_cont.
      * eassumption.
      * constructor. congruence.
    - simpl. inversion H. repeat constructor. congruence.
    - simpl. rewrite <- app_assoc. inversion H. eapply compiled_expr_correct_cont.
      * eassumption.
      * constructor. congruence.
    - simpl. inversion H. congruence.
    - simpl. rewrite <- app_assoc.
      inversion H. subst.
      destruct c' as [[]].
      eapply IHSp1; try eassumption. 
      eapply IHSp2; eassumption.
  Qed.
  
  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    rewrite <- (app_nil_r (compile p Sp)).
    eapply compiled_straightline_correct_cont; try eassumption. 
    constructor. remember ([R]) as pr. assumption. 
  Qed.
  
  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof. 
    dependent induction Sp.
    - simpl in EXEC. rewrite <- app_assoc in EXEC. apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [n [EVAL EXEC]].
      inversion EXEC; subst.
      repeat eexists; eauto.
    - simpl in EXEC. inversion EXEC; subst. inversion EXEC0; subst.
      repeat eexists; eauto.
    - simpl in EXEC. rewrite <- app_assoc in EXEC. apply compiled_expr_not_incorrect_cont in EXEC. 
      destruct EXEC as [n [EVAL EXEC]].
      inversion EXEC; subst.
      repeat eexists; eauto.
    - simpl in EXEC. repeat eexists; eauto.
    - simpl in EXEC. rewrite <- app_assoc in EXEC. apply IHSp1 in EXEC.
      destruct EXEC as [st1 [i1 [o1 [EVAL1 EXEC]]]]. 
      apply IHSp2 in EXEC.
      destruct EXEC as [st2 [i2 [o2 [EVAL2 EXEC]]]]. 
      repeat eexists; eauto.
  Qed.
  
  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof.
    rewrite <- (app_nil_r (compile p Sp)) in EXEC.
    apply compiled_straightline_not_incorrect_cont in EXEC.
    destruct EXEC as [st1 [i1 [o1 [EVAL1 EXEC]]]]. 
    inversion EXEC. congruence.
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
  - simpl. rewrite Bool.andb_true_r. assumption.
  - destruct a; try auto; simpl in *; apply andb_prop in Hwf; destruct Hwf; rewrite H; auto.
Qed.

Lemma wf_jz (p q  : prog)
             (l    : nat)
             (Hwf  : prog_wf_rec q p = true)
             (Hocc : label_occurs_once l q = true) : prog_wf_rec q (p ++ [JZ l]) = true.
Proof. 
  induction p.
  - simpl. rewrite Bool.andb_true_r. assumption.
  - destruct a; try auto; simpl in *; apply andb_prop in Hwf; destruct Hwf; rewrite H; auto.
Qed.

Lemma wf_jnz (p q  : prog)
             (l    : nat)
             (Hwf  : prog_wf_rec q p = true)
             (Hocc : label_occurs_once l q = true) : prog_wf_rec q (p ++ [JNZ l]) = true.
Proof. 
  induction p.
  - simpl. rewrite Bool.andb_true_r. assumption.
  - destruct a; try auto; simpl in *; apply andb_prop in Hwf; destruct Hwf; rewrite H; auto.
Qed.

Lemma wf_lab (p q  : prog)
             (l    : nat)
             (Hwf  : prog_wf_rec q p = true) : prog_wf_rec q (p ++ [LAB l]) = true.
Proof. 
  induction p.
  - reflexivity.
  - destruct a; try auto; simpl in *; apply andb_prop in Hwf; destruct Hwf; rewrite H; auto.
Qed.

Lemma wf_b (p q  : prog) l
             (Hwf  : prog_wf_rec q p = true) : prog_wf_rec q (p ++ [B l]) = true.
Proof. 
  induction p.
  - reflexivity.
  - destruct a; try auto; simpl in *; apply andb_prop in Hwf; destruct Hwf; rewrite H; auto.
Qed.

Lemma wf_rev (p q : prog) (Hwf : prog_wf_rec q p = true) : prog_wf_rec q (rev p) = true.
Proof.
  induction p.
  - reflexivity.
  - simpl. destruct a.
    * simpl in Hwf. apply andb_prop in Hwf. destruct Hwf. apply wf_app; auto.
    * simpl in Hwf. apply andb_prop in Hwf. destruct Hwf. apply wf_jz; auto.
    * simpl in Hwf. apply andb_prop in Hwf. destruct Hwf. apply wf_jnz; auto.
    * simpl in Hwf. apply wf_lab; auto.
    * simpl in Hwf. apply wf_b; auto.
Qed.


Fixpoint convert_straightline (p : StraightLine.prog) : prog :=
  match p with
    []      => []
  | i :: p' => B i :: convert_straightline p'
  end.

Lemma cons_comm_app (A : Type) (a : A) (l1 l2 : list A) : l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof. rewrite <- app_assoc. reflexivity. Qed.

Definition compile_expr (e : expr) : prog :=
  convert_straightline (StraightLine.compile_expr e).
