Require Import BinInt ZArith_dec.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Export Id.
Require Export State.
Require Export Expr.
Require Export Stmt.

From hahn Require Import HahnBase.

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
  
  (* Partial correctness of expression compiler *)
  Lemma compiled_expr_correct_cont
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (p : prog) (c : conf)
        (VAL : [| e |] st => n)
        (EXEC: (n::s, st, i, o) -- p --> c) :        
    (s, st, i, o) -- (compile_expr e) ++ p --> c.
  Proof. 
    dependent induction VAL generalizing p s i o.
    { apply sm_Const. assumption. }
    { eapply sm_Load. eassumption. assumption. }
    all: simpl; (repeat rewrite <- app_assoc); eapply IHVAL1; eapply IHVAL2.
    { apply sm_Add. assumption. assumption. }
    { apply sm_Sub. assumption. assumption. }
    { apply sm_Mul. assumption. }
    { apply sm_Div. assumption. assumption. }
    { apply sm_Mod. assumption. assumption. }
    { apply sm_Le_T. assumption. assumption. }
    { apply sm_Le_F. assumption. assumption. }
    { apply sm_Lt_T. assumption. assumption. }
    { apply sm_Lt_F. assumption. assumption. }
    { apply sm_Ge_T. assumption. assumption. }
    { apply sm_Ge_F. assumption. assumption. }
    { apply sm_Gt_T. assumption. assumption. }
    { apply sm_Gt_F. assumption. assumption. }
    { apply sm_Eq_T. assumption. assumption. }
    { apply sm_Eq_F. assumption. assumption. }
    { apply sm_Ne_T. assumption. assumption. }
    { apply sm_Ne_F. assumption. assumption. }
    { apply sm_And. assumption. assumption. assumption. }
    apply sm_Or. assumption. assumption. assumption.
  Qed.

  #[export] Hint Resolve compiled_expr_correct_cont.
  
  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof. 
    remember (compiled_expr_correct_cont e st s i o n ([]) (n::s, st, i, o)).
    assert (((n :: s, st, i, o)) -- [] --> ((n :: s, st, i, o))). 
    { constructor. exact []. }
    remember (s0 VAL H). 
    clear Heqs1 Heqs0.
    assert ((compile_expr e) ++ [] = compile_expr e).
    { apply app_nil_r. }
    rewrite <- H0. assumption.
  Qed.
  
  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof.
    dependent induction e; simpl in EXEC.
    { assert ([|Nat z|] st => (z) /\ ((z :: s, st, i, o)) -- p --> (c)).
      { split.
        { constructor. }
        inv EXEC. }
      eauto. }
    { inv EXEC. 
      assert ([|Var i|] st => (z) /\ ((z :: s, st, i0, o)) -- p --> (c)).
      { split.
        { constructor. assumption. }
        assumption. }
      eauto. }
    repeat rewrite <- app_assoc in EXEC.
    remember (IHe1 st s i o (compile_expr e2 ++ [B b] ++ p) c EXEC). 
    destruct e as [za [E1 P0]].
    remember (IHe2 st (za::s) i o ([B b] ++ p) c P0).
    destruct e as [zb [E2 P1]]. clear Heqe Heqe0.
    simpl in P1. inv P1; eauto.
  Qed.
  
  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof. 
    dependent induction e; simpl in EXEC.
    { inv EXEC. inv EXEC0. }
    { inv EXEC. inv EXEC0. constructor. assumption. }
    remember (compiled_expr_not_incorrect_cont e1 st s i o (compile_expr e2 ++ [B b]) (n :: s, st, i, o) EXEC).
    destruct e. destruct a.
    remember (compiled_expr_not_incorrect_cont e2 st (x :: s) i o ([B b]) (n :: s, st, i, o) s0).
    destruct e0. destruct a.
    destruct b; inv s1; inv EXEC0.
    { eapply bs_Add; eassumption. }
    { eapply bs_Sub; eassumption. }
    { eapply bs_Mul; eassumption. }
    { eapply bs_Div; eassumption. }
    { eapply bs_Mod; eassumption. }
    { eapply bs_Le_T; eassumption. }
    { eapply bs_Le_F; eassumption. }
    { eapply bs_Lt_T; eassumption. }
    { eapply bs_Lt_F; eassumption. }
    { eapply bs_Ge_T; eassumption. }
    { eapply bs_Ge_F; eassumption. }
    { eapply bs_Gt_T; eassumption. }
    { eapply bs_Gt_F; eassumption. }
    { eapply bs_Eq_T; eassumption. }
    { eapply bs_Eq_F; eassumption. }
    { eapply bs_Ne_T; eassumption. }
    { eapply bs_Ne_F; eassumption. }
    { eapply bs_And; eassumption. }
    eapply bs_Or; eassumption.
  Qed.
  
  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof. 
    split; intro. 
    { eapply compiled_expr_not_incorrect. eassumption. }
    apply compiled_expr_correct. assumption.
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
    dependent induction Sp; simpl; inv H; try (rewrite <- app_assoc).
    { eapply compiled_expr_correct_cont. eassumption.
      eapply sm_Store. eassumption. }
    { eapply sm_Read. eapply sm_Store. eassumption. }
    { eapply compiled_expr_correct_cont. eassumption.
      eapply sm_Write. eassumption. }
    destruct c' as [[st'' i''] o'']. eapply IHSp1; try eassumption.
    eapply IHSp2; eassumption.
  Qed.
    
  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    remember (compiled_straightline_correct_cont p Sp st st' ([]) i o ([]) i' o' EXEC ([]) (([]), st', i', o')).
    assert ((([], st', i', o')) -- [] --> (([], st', i', o'))). { apply sm_End. exact ([]). }
    remember (s H). assert (compile p Sp ++ [] = compile p Sp). { apply app_nil_r. }
    rewrite <- H0. assumption.
  Qed.
  
  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof.
    dependent induction Sp; simpl in EXEC; try (rewrite <- app_assoc in EXEC).
    { eapply compiled_expr_not_incorrect_cont in EXEC. destruct EXEC. destruct H.
      exists ((st)[x <- x0]). exists i. exists o. split. auto. inv H0. }
    { inv EXEC. inv EXEC0. exists ((st)[x <- z]). exists i0. exists o. split.
      auto. assumption. }
    { eapply compiled_expr_not_incorrect_cont in EXEC. destruct EXEC. destruct H.
      inv H0. exists st. exists i. exists (x :: o). split. auto. assumption. }
    { exists st. exists i. exists o. split. auto. assumption. }
    eapply IHSp1 in EXEC. destruct EXEC. destruct H. destruct H. destruct H.
    eapply IHSp2 in H0. destruct H0. destruct H0. destruct H0. destruct H0.
    exists x2. exists x3. exists x4. split. eapply bs_Seq; eassumption. assumption.
  Qed.

  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof. 
    dependent induction Sp; simpl in EXEC; try (rewrite <- app_assoc in EXEC).
    { eapply compiled_expr_not_incorrect_cont in EXEC. destruct EXEC as [n [BS COMP]].
      inv COMP. inv EXEC. auto. }
    { inv EXEC. inv EXEC0. inv EXEC1. }
    { eapply compiled_expr_not_incorrect_cont in EXEC. destruct EXEC as [n [BS COMP]].
      inv COMP. inv EXEC. auto. }
    { inv EXEC. }
    eapply compiled_straightline_not_incorrect_cont in EXEC.
    destruct EXEC as [st0 [i0 [o0 [BS COMP]]]]. eapply IHSp2 in COMP. eapply bs_Seq; eassumption.
  Qed.
  
  Theorem straightline_compiler_correct
          (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z) :
    (st, i, o) == p ==> (st', i', o') <-> ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    split; intro.
    { apply compiled_straightline_correct. assumption. }
    eapply compiled_straightline_not_incorrect. eassumption.
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
  { simpl. rewrite -> Hocc. auto. }
  destruct a. simpl.
  { apply Bool.andb_true_iff in Hwf. destruct Hwf as (Ha & Hb). 
    remember (IHp Hb). rewrite -> e. inv Hocc. }
  { inv Hwf. apply Bool.andb_true_iff in H0. destruct H0 as (Ha & Hb).
    remember (IHp Hb). simpl. rewrite -> e. inv Hocc. }
  { inv Hwf. apply Bool.andb_true_iff in H0. destruct H0 as (Ha & Hb).
    remember (IHp Hb). simpl. rewrite -> e. inv Hocc. }
  { inv Hwf. assert (true = true). { auto. }
    remember (IHp H). simpl. assumption. }
  { inv Hwf. assert (true = true). { auto. }
    remember (IHp H). simpl. assumption. }
Qed.

Lemma wf_rev (p q : prog) (Hwf : prog_wf_rec q p = true) : prog_wf_rec q (rev p) = true.
Proof.
  induction p; simpl; auto.
  destruct a; inv Hwf; remember (rev p) as p'.
  { apply Bool.andb_true_iff in H0. destruct H0 as (Ha & Hb).
    remember (IHp Hb). eapply wf_app; auto. }
  { apply Bool.andb_true_iff in H0. destruct H0 as (Ha & Hb).
    remember (IHp Hb). dependent induction p'.
    { simpl. rewrite -> Ha. auto. }
    destruct a; simpl. admit. }
  (* Too much code-duplication here *)
  Admitted.

Fixpoint convert_straightline (p : StraightLine.prog) : prog :=
  match p with
    []      => []
  | i :: p' => B i :: convert_straightline p'
  end.

Lemma cons_comm_app (A : Type) (a : A) (l1 l2 : list A) : l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof. 
  induction l1; auto.
  rewrite <- app_assoc. simpl. reflexivity.
Qed.

Definition compile_expr (e : expr) : prog :=
  convert_straightline (StraightLine.compile_expr e).
