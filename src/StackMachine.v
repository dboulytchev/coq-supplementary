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
    revert s i o n p c VAL EXEC.
    induction e as [n0 | x | op e1 IHe1 e2 IHe2]; intros s i o n p c VAL EXEC.
    - inversion VAL; subst. simpl. eapply sm_Const. exact EXEC.
    - inversion VAL; subst. simpl. eapply sm_Load; [exact VAR | exact EXEC].
    - simpl. rewrite <- app_assoc.
      inversion VAL; subst;
      (eapply IHe1; [eassumption | rewrite <- app_assoc; eapply IHe2; [eassumption | simpl;
        first [ eapply sm_Add; solve [assumption | exact EXEC]
              | eapply sm_Sub; solve [assumption | exact EXEC]
              | eapply sm_Mul; solve [assumption | exact EXEC]
              | eapply sm_Div; solve [assumption | exact EXEC]
              | eapply sm_Mod; solve [assumption | exact EXEC]
              | eapply sm_Le_T; solve [assumption | exact EXEC]
              | eapply sm_Le_F; solve [assumption | exact EXEC]
              | eapply sm_Ge_T; solve [assumption | exact EXEC]
              | eapply sm_Ge_F; solve [assumption | exact EXEC]
              | eapply sm_Lt_T; solve [assumption | exact EXEC]
              | eapply sm_Lt_F; solve [assumption | exact EXEC]
              | eapply sm_Gt_T; solve [assumption | exact EXEC]
              | eapply sm_Gt_F; solve [assumption | exact EXEC]
              | eapply sm_Eq_T; solve [assumption | exact EXEC]
              | eapply sm_Eq_F; solve [assumption | exact EXEC]
              | eapply sm_Ne_T; solve [assumption | exact EXEC]
              | eapply sm_Ne_F; solve [assumption | exact EXEC]
              | eapply sm_And; solve [assumption | exact EXEC]
              | eapply sm_Or; solve [assumption | exact EXEC] ] ] ]).
    Unshelve. all: exact [].
  Qed.

  #[export] Hint Resolve compiled_expr_correct_cont.
  
  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof.
    rewrite <- (app_nil_r (compile_expr e)).
    eapply compiled_expr_correct_cont; [exact VAL | constructor].
    Unshelve. exact [].
  Qed.
  
  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof.
    revert s i o p c EXEC.
    induction e as [n0 | x | op e1 IHe1 e2 IHe2]; intros s i o p c EXEC.
    - simpl in EXEC. inversion EXEC; subst.
      exists n0. split; [constructor | assumption].
    - simpl in EXEC. inversion EXEC; subst.
      exists z. split; [constructor; assumption | assumption].
    - simpl in EXEC. rewrite <- app_assoc in EXEC.
      apply IHe1 in EXEC. destruct EXEC as [za [VALA EXEC1]].
      rewrite <- app_assoc in EXEC1.
      apply IHe2 in EXEC1. destruct EXEC1 as [zb [VALB EXEC2]].
      simpl in EXEC2.
      inversion EXEC2; subst;
      [ (exists (za + zb)%Z; split; [eapply bs_Add; eauto | assumption])
      | (exists (za - zb)%Z; split; [eapply bs_Sub; eauto | assumption])
      | (exists (za * zb)%Z; split; [eapply bs_Mul; eauto | assumption])
      | (exists (Z.div za zb); split; [eapply bs_Div; eauto | assumption])
      | (exists (Z.modulo za zb); split; [eapply bs_Mod; eauto | assumption])
      | (exists Z.one; split; [eapply bs_Le_T; eauto | assumption])
      | (exists Z.zero; split; [eapply bs_Le_F; eauto | assumption])
      | (exists Z.one; split; [eapply bs_Ge_T; eauto | assumption])
      | (exists Z.zero; split; [eapply bs_Ge_F; eauto | assumption])
      | (exists Z.one; split; [eapply bs_Lt_T; eauto | assumption])
      | (exists Z.zero; split; [eapply bs_Lt_F; eauto | assumption])
      | (exists Z.one; split; [eapply bs_Gt_T; eauto | assumption])
      | (exists Z.zero; split; [eapply bs_Gt_F; eauto | assumption])
      | (exists Z.one; split; [eapply bs_Eq_T; eauto | assumption])
      | (exists Z.zero; split; [eapply bs_Eq_F; eauto | assumption])
      | (exists Z.one; split; [eapply bs_Ne_T; eauto | assumption])
      | (exists Z.zero; split; [eapply bs_Ne_F; eauto | assumption])
      | (exists (za * zb)%Z; split; [eapply bs_And; eauto | assumption])
      | (exists (zor za zb); split; [eapply bs_Or; eauto | assumption])
      ].
  Qed.
  
  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof.
    rewrite <- (app_nil_r (compile_expr e)) in EXEC.
    apply compiled_expr_not_incorrect_cont in EXEC.
    destruct EXEC as [n' [VAL EXEC']].
    inversion EXEC'; subst. assumption.
  Qed.

  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof.
    split; [apply compiled_expr_not_incorrect | apply compiled_expr_correct].
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
    revert st st' i o i' o' H q c EXEC.
    induction Sp as [x e | x | e | | s1 s2 Sp1 IH1 Sp2 IH2]; intros st st' i o i' o' H q c EXEC.
    - inversion H; subst. simpl. rewrite <- app_assoc.
      eapply compiled_expr_correct_cont; [exact VAL | eapply sm_Store; exact EXEC].
    - inversion H; subst. simpl.
      eapply sm_Read. eapply sm_Store. exact EXEC.
    - inversion H; subst. simpl. rewrite <- app_assoc.
      eapply compiled_expr_correct_cont; [exact VAL | eapply sm_Write; exact EXEC].
    - inversion H; subst. simpl. exact EXEC.
    - inversion H; subst.
      destruct c' as [[st1 i1] o1].
      simpl. rewrite <- app_assoc.
      eapply IH1; [exact STEP1 | eapply IH2; [exact STEP2 | exact EXEC]].
  Qed.

  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    rewrite <- (app_nil_r (compile p Sp)).
    eapply (compiled_straightline_correct_cont p Sp st st' (@nil Z) i o (@nil Z) i' o' EXEC).
    constructor.
    Unshelve. all: exact [].
  Qed.

  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof.
    revert st i o q c EXEC.
    induction Sp as [x e | x | e | | s1 s2 Sp1 IH1 Sp2 IH2]; intros st i o q c EXEC.
    - simpl in EXEC. rewrite <- app_assoc in EXEC.
      apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [z [VAL EXEC1]].
      simpl in EXEC1. inversion EXEC1; subst.
      exists (st [x <- z]), i, o. split; [constructor; assumption | assumption].
    - simpl in EXEC. inversion EXEC; subst.
      inversion EXEC0; subst.
      exists (st [x <- z]), i0, o. split; [constructor | assumption].
    - simpl in EXEC. rewrite <- app_assoc in EXEC.
      apply compiled_expr_not_incorrect_cont in EXEC.
      destruct EXEC as [z [VAL EXEC1]].
      simpl in EXEC1. inversion EXEC1; subst.
      exists st, i, (z :: o). split; [constructor; assumption | assumption].
    - simpl in EXEC.
      exists st, i, o. split; [constructor | exact EXEC].
    - simpl in EXEC. rewrite <- app_assoc in EXEC.
      apply IH1 in EXEC.
      destruct EXEC as [st1 [i1 [o1 [STEP1 EXEC1]]]].
      apply IH2 in EXEC1.
      destruct EXEC1 as [st' [i' [o' [STEP2 EXEC2]]]].
      exists st', i', o'. split; [eapply bs_Seq; [exact STEP1 | exact STEP2] | exact EXEC2].
  Qed.

  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof.
    rewrite <- (app_nil_r (compile p Sp)) in EXEC.
    apply compiled_straightline_not_incorrect_cont in EXEC.
    destruct EXEC as [st1 [i1 [o1 [H EXEC1]]]].
    inversion EXEC1; subst. exact H.
  Qed.

  Theorem straightline_compiler_correct
          (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z) :
    (st, i, o) == p ==> (st', i', o') <-> ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof.
    split; [apply compiled_straightline_correct | apply compiled_straightline_not_incorrect].
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

Lemma wf_app_gen (p q : prog) (i : insn)
      (Hwf : prog_wf_rec q p = true)
      (Hi : match i with
            | JMP l | JZ l | JNZ l => label_occurs_once l q
            | _ => true
            end = true) :
  prog_wf_rec q (p ++ [i]) = true.
Proof.
  induction p as [ | i' p' IH].
  - simpl. rewrite Bool.andb_true_r. exact Hi.
  - simpl in Hwf |- *.
    apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hi' Hp'].
    apply Bool.andb_true_iff. split.
    + exact Hi'.
    + apply IH. exact Hp'.
Qed.

Lemma wf_app (p q  : prog)
             (l    : nat)
             (Hwf  : prog_wf_rec q p = true)
             (Hocc : label_occurs_once l q = true) : prog_wf_rec q (p ++ [JMP l]) = true.
Proof. apply wf_app_gen; [exact Hwf | exact Hocc]. Qed.

Lemma wf_rev (p q : prog) (Hwf : prog_wf_rec q p = true) : prog_wf_rec q (rev p) = true.
Proof.
  induction p as [ | i p' IH].
  - reflexivity.
  - simpl in Hwf. apply Bool.andb_true_iff in Hwf. destruct Hwf as [Hi Hp'].
    simpl. apply wf_app_gen.
    + apply IH. exact Hp'.
    + exact Hi.
Qed.

Fixpoint convert_straightline (p : StraightLine.prog) : prog :=
  match p with
    []      => []
  | i :: p' => B i :: convert_straightline p'
  end.

Lemma cons_comm_app (A : Type) (a : A) (l1 l2 : list A) : l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof. exact (app_assoc l1 (a :: nil) l2). Qed.

Definition compile_expr (e : expr) : prog :=
  convert_straightline (StraightLine.compile_expr e).
