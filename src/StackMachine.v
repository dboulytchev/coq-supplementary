Require Import BinInt ZArith_dec.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Export Id.
Require Export State.
Require Export Expr.
Require Export Stmt.

Require Import Stdlib.Program.Equality.

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
  Proof. generalize dependent c. generalize dependent n. generalize dependent p. generalize dependent s.
  induction e; intros.
  - simpl. apply sm_Const. replace z with n by (inversion VAL; auto). apply EXEC.
  - simpl. apply sm_Load with (z := n).
    + inversion VAL. auto.
    + apply EXEC.
  - simpl.
    replace (((compile_expr e1) ++ ((compile_expr e2) ++ [B b])) ++ p) with
      ((compile_expr e1) ++ ((compile_expr e2) ++ ([B b] ++ p))).
    + inversion VAL;
      apply IHe1 with (n := za); auto;
      apply IHe2 with (n := zb); auto;
      try (constructor; subst;
      (* Somehow the magic word `progress` makes `constructor` select the right constructor *)
      (* And, even more curious, without `try` on previous line, it hangs for several minutes *)
      progress auto).
    + rewrite app_assoc. rewrite app_assoc. f_equal. rewrite <- app_assoc. reflexivity.
  Qed.

  #[export] Hint Resolve compiled_expr_correct_cont.
  
  Lemma compiled_expr_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z)
        (VAL : [| e |] st => n) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o).
  Proof. induction e.
  - simpl. inversion VAL. subst. apply sm_Const. apply (sm_End ([]) _).
  - simpl. inversion VAL. subst. apply sm_Load with (z := n); auto. apply (sm_End ([]) _).
  - simpl. inversion VAL;
    subst; apply compiled_expr_correct_cont with (n := za); auto;
    apply compiled_expr_correct_cont with (n := zb); auto.
    (* This thing hangs forever if not unwinded *)
    + repeat constructor.
    + repeat constructor.
    + repeat constructor.
    + repeat constructor. congruence.
    + repeat constructor. congruence.
    + repeat (constructor; auto).
    + repeat constructor; progress auto.
    + repeat (constructor; auto).
    + repeat constructor; progress auto.
    + repeat constructor; progress auto.
    + repeat constructor; progress auto.
    + repeat constructor; progress auto.
    + repeat constructor; progress auto.
    + repeat constructor; progress auto.
    + repeat constructor; progress auto.
    + repeat constructor; progress auto.
    + repeat constructor; progress auto.
    + repeat (constructor; auto).
    + repeat (constructor; auto).
  Qed.

  Lemma compile_expr_eval_ex (e: expr) (st: state Z) (s i o: list Z) (p: prog) (c: conf)
      (EXEC: (s, st, i, o) --compile_expr e ++ p--> c):
    exists (n: Z), [|e|] st => n.
  Proof. induction e.
  - econstructor. auto.
  - inversion EXEC. subst. exists z. auto.
  - (* Looks like the only way is `destruct b`... *) admit.
  Admitted.

  (* Maybe there is a way to reduce the number of arguments, but this thing is used once *)
  Ltac compiled_expr_not_incorrect_cont_b_case_internal b H EXEC za zb s st i o e1 e2 p c IHe1 IHe2 :=
  simpl in EXEC; rewrite <- app_assoc in EXEC;
  assert (za :: s, st, i, o) --((compile_expr e2) ++ [B b]) ++ p--> c as EXEC1 by
    ( specialize IHe1 with s (((compile_expr e2) ++ [B b]) ++ p) c za;
      apply IHe1 in EXEC as EXEC1; auto; destruct EXEC1 as [n1 [VALA' EXEC1']];
      assert (n1 = za) by (eauto using eval_deterministic); subst;
      apply EXEC1' );
  rewrite <- app_assoc in EXEC1;
  assert ((zb :: za :: s, st, i, o) --[B b] ++ p--> c) as EXEC2 by
    ( specialize IHe2 with (za :: s) ([B b] ++ p) c zb;
      apply IHe2 in EXEC1 as EXEC2; auto; destruct EXEC2 as [n2 [VALB' EXEC2']];
      assert (n2 = zb) by (eauto using eval_deterministic); subst;
      apply EXEC2' );
  inversion EXEC2; auto; congruence.

  Ltac compiled_expr_not_incorrect_cont_b_case_arithm b H EXEC za zb s st i o e1 e2 p c IHe1 IHe2 :=
  inversion H; subst;
  compiled_expr_not_incorrect_cont_b_case_internal b H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.

  Ltac compiled_expr_not_incorrect_cont_b_case_rel b H EXEC za zb s st i o e1 e2 p c IHe1 IHe2 :=
  inversion H; subst;
  (* Relations have two constructors each, so we need some extra case analysis here *)
  (compiled_expr_not_incorrect_cont_b_case_internal b H EXEC za zb s st i o e1 e2 p c IHe1 IHe2) +
  (compiled_expr_not_incorrect_cont_b_case_internal b H EXEC za zb s st i o e1 e2 p c IHe1 IHe2).

  Lemma compiled_expr_not_incorrect_cont
        (e : expr) (st : state Z) (s i o : list Z) (p : prog) (c : conf)
        (EXEC : (s, st, i, o) -- compile_expr e ++ p --> c) :
    exists (n : Z), [| e |] st => n /\ (n :: s, st, i, o) -- p --> c.
  Proof. assert (exists n, [|e|] st => n). { eauto using compile_expr_eval_ex. }
  destruct H as [n].
  generalize dependent n. generalize dependent c. generalize dependent p. generalize dependent s.
  induction e; intros;
  exists n; split; auto.
  - simpl in EXEC. inversion H. subst. inversion EXEC. auto.
  - simpl in EXEC. inversion H. subst. inversion EXEC. subst.
    assert (z = n). { eapply state_deterministic; eauto. }
    subst. auto.
  - destruct b.
    (* Arithmetic *)
    + compiled_expr_not_incorrect_cont_b_case_arithm Add H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_arithm Sub H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_arithm Mul H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_arithm Div H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_arithm Mod H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    (* Relations *)
    + compiled_expr_not_incorrect_cont_b_case_rel Le H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_rel Lt H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_rel Ge H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_rel Gt H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_rel Eq H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_rel Ne H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    (* Logic *)
    + compiled_expr_not_incorrect_cont_b_case_arithm And H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
    + compiled_expr_not_incorrect_cont_b_case_arithm Or H EXEC za zb s st i o e1 e2 p c IHe1 IHe2.
  Qed.

  Lemma compile_expr_not_nil (e: expr):
    compile_expr e <> [].
  Proof. intros H. induction e.
  - simpl in H. discriminate H.
  - simpl in H. discriminate H.
  - simpl in H. assert (((compile_expr e1 ++ compile_expr e2) ++ [B b]) <> []).
      { symmetry. apply (app_cons_not_nil (compile_expr e1 ++ compile_expr e2) ([])). }
    rewrite app_assoc in H. congruence.
  Qed.

  Lemma compile_expr_hd (e: expr) (h: insn) (t: list insn) (EQ: compile_expr e = h :: t):
    (exists x, h = L x) \/ (exists n, h = C n).
  Proof. generalize dependent h. generalize dependent t. induction e; intros.
  - simpl in EQ. inversion EQ. subst. right. exists z. reflexivity.
  - simpl in EQ. inversion EQ. subst. left. exists i. reflexivity.
  - simpl in EQ.
    specialize compile_expr_not_nil with e1 as NE1.
    destruct (compile_expr e1); try congruence. clear NE1.
    apply IHe1 with (t := l). inversion EQ. reflexivity.
  Qed.

  (* Couldn't find this fact in stdlib *)
  Lemma cons_not_id (T: Type) (t: list T) (h: T): h :: t <> t.
  Proof. intros H. assert (length (h :: t) = length t).
    { f_equal. apply H. }
  simpl in H0. lia. Qed.

  (* A trivial fact, that cannot be proven very elegantly *)
  Lemma app_to_end_neq (T: Type) (back1 back2: T) (body1 body2: list T) (NEQ: back1 <> back2):
    body1 ++ [back1] <> body2 ++ [back2].
  Proof. intros H. apply NEQ. assert (last (body1 ++ [back1]) back1 = last (body2 ++ [back2]) back1).
    { f_equal. auto. }
  rewrite last_last in H0. rewrite last_last in H0. auto.
  Qed.

  (* It's clear from the definition of compile_expr, but I can't find an easy way to make Coq realize this *)
  Lemma compile_var (e: expr) (x: id) (COMP: compile_expr e = [L x]):
    e = Var x.
  Proof.
  destruct e.
  - simpl in COMP. discriminate COMP.
  - simpl in COMP. inversion COMP. auto.
  - simpl in COMP. assert (B b <> L x) by congruence.
    apply app_to_end_neq with (body1 := (compile_expr e1 ++ compile_expr e2)) (body2 := []) in H.
    rewrite app_assoc in COMP. destruct H. auto.
  Qed.

  (* Same *)
  Lemma compile_const (e: expr) (z: Z) (COMP: compile_expr e = [C z]):
    e = Nat z.
  Proof. destruct e.
  - simpl in COMP. inversion COMP. auto.
  - simpl in COMP. discriminate COMP.
  - simpl in COMP. assert (B b <> C z) by congruence.
    apply app_to_end_neq with (body1 := (compile_expr e1 ++ compile_expr e2)) (body2 := []) in H.
    rewrite app_assoc in COMP. destruct H. auto.
  Qed.

  Lemma compile_dec (e: expr):
    {exists n, compile_expr e = [C n]} +
    {exists x, compile_expr e = [L x]} +
    {exists b e1 e2, compile_expr e = compile_expr e1 ++ compile_expr e2 ++ [B b]}.
  Proof. destruct e.
  - left. left. exists z. reflexivity.
  - left. right. exists i. reflexivity.
  - right. exists b. exists e1. exists e2. reflexivity.
  Qed.

  Lemma compile_bop (e e1 e2: expr) (b: bop) (COMP: compile_expr e = compile_expr e1 ++ compile_expr e2 ++ [B b]):
    e = Bop b e1 e2.
  Proof. destruct e.
  - inversion COMP. assert (C z <> B b) by congruence.
    apply app_to_end_neq with (body1 := []) (body2 := compile_expr e1 ++ compile_expr e2) in H.
    rewrite <- app_assoc in H. destruct H. auto.
  - inversion COMP. assert (L i <> B b) by congruence.
    apply app_to_end_neq with (body1 := []) (body2 := compile_expr e1 ++ compile_expr e2) in H.
    rewrite <- app_assoc in H. destruct H. auto.
  - (* Here we need injectivity of compile, i. e. unambiguity of inverse polish notation *) admit.
  Admitted.

(* Maybe this will be more convenient:
  destruct (compile_dec e) as [[s1 | s2] | s3].
  - destruct s1. rewrite H in COMP.
    specialize app_to_end_neq with
        (back1 := C x) (back2 := B b) (body1 := []) (body2 := compile_expr e1 ++ compile_expr e2) as APP_END.
    destruct APP_END.
    + congruence.
    + simpl. rewrite <- app_assoc. apply COMP.
  - admit.
  - *)

  Lemma length_not_nil (T: Type) (l: list T):
    l <> [] <-> length l > 0.
  Proof. destruct l;
  simpl; split; intros;
  (congruence || lia).
  Qed.

  Lemma compiled_length (e: expr):
    length (compile_expr e) > 1 <-> exists b e1 e2, compile_expr e = compile_expr e1 ++ compile_expr e2 ++ [B b].
  Proof. split; intros.
  - destruct (compile_dec e) as [[s1 | s2] | s3].
    + destruct s1 as [n]. rewrite H0 in H. simpl in H. lia.
    + destruct s2 as [x]. rewrite H0 in H. simpl in H. lia.
    + apply s3.
  - destruct H as [b [e1 [e2]]]. rewrite H. repeat rewrite length_app. simpl.
    specialize compile_expr_not_nil with e1 as NNIL1. rewrite length_not_nil in NNIL1. lia.
  Qed.

  Lemma compiled_expr_not_incorrect
        (e : expr) (st : state Z)
        (s i o : list Z) (n : Z)
        (EXEC : (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o)) :
    [| e |] st => n.
  Proof. dependent induction EXEC;
  try (symmetry in x; apply compile_expr_hd in x; destruct x as [[x H] | [x H]]; discriminate H).
  - symmetry in x0. apply compile_expr_not_nil in x0. destruct x0.
  - symmetry in x. apply compile_expr_hd in x as x1. destruct x1 as [[var H] | [var H]]; try discriminate H.
    inversion H. subst. clear H.

    destruct q.
    + inversion EXEC. subst. apply compile_var in x. subst. auto.
    + assert (length (compile_expr e) > 1) as LEN. { rewrite x. simpl. lia. }
      rewrite compiled_length in LEN. destruct LEN as [b [e1 [e2]]].
      assert (e = Bop b e1 e2). { apply compile_bop in H. auto. } subst.
      (* Here we got bad induction hypothesis. Maybe a properly stated lemma may help *)
      admit.

  - symmetry in x.

    destruct q.
    + inversion EXEC. subst. apply compile_const in x. subst. auto.
    + (* Same *) admit.
  Admitted.

  Lemma expr_compiler_correct
        (e : expr) (st : state Z) (s i o : list Z) (n : Z) :
    (s, st, i, o) -- (compile_expr e) --> (n::s, st, i, o) <-> [| e |] st => n.
  Proof. split; intros.
  - apply compiled_expr_not_incorrect in H. auto.
  - apply compiled_expr_correct. auto.
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
  generalize dependent st. generalize dependent s. generalize dependent i. generalize dependent o.
  generalize dependent st'. generalize dependent s'. generalize dependent i'. generalize dependent o'.
  generalize dependent c.
  generalize dependent q.
  induction Sp; intros;
  inversion H; subst; simpl.
  - rewrite <- app_assoc. apply compiled_expr_correct_cont with (n := z); auto.
    constructor. auto.
  - constructor. constructor. auto.
  - rewrite <- app_assoc. apply compiled_expr_correct_cont with (n := z); auto.
    constructor. auto.
  - auto.
  - rewrite <- app_assoc.
    destruct c' as [[stc ic] oc].
    assert ([], stc, ic, oc) --compile s2 Sp2 ++ q--> c.
      { apply IHSp2 with (st' := st') (i' := i') (o' := o'); auto. }
    apply IHSp1 with (st' := stc) (i' := ic) (o' := oc); auto.
  Qed.

  Lemma compiled_straightline_correct
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : (st, i, o) == p ==> (st', i', o')) :
    ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof. replace (compile p Sp) with (compile p Sp ++ []).
  - assert ([], st', i', o') --[]--> ([], st', i', o').
      { repeat constructor. }
    apply compiled_straightline_correct_cont with (st' := st') (i' := i') (o' := o'); auto.
  - apply app_nil_r.
  Qed.

  Lemma compiled_straightline_not_incorrect_cont
        (p : stmt) (Sp : StraightLine p) (st : state Z) (i o : list Z) (q : prog) (c : conf)
        (EXEC: ([], st, i, o) -- (compile p Sp) ++ q --> c) :
    exists (st' : state Z) (i' o' : list Z), (st, i, o) == p ==> (st', i', o') /\ ([], st', i', o') -- q --> c.
  Proof. generalize dependent q.
  generalize dependent st. generalize dependent i. generalize dependent o.
  induction Sp; intros.
  - simpl in EXEC. rewrite <- app_assoc in EXEC. apply compiled_expr_not_incorrect_cont in EXEC as STEP1.
    destruct STEP1 as [n [EVAL1 COMP1]]. inversion COMP1. subst.
    exists (st [x <- n]). exists i. exists o. auto.
  - simpl in EXEC. inversion EXEC. inversion EXEC0. subst.
    exists (st [x <- z]). exists i0. exists o. auto.
  - simpl in EXEC. rewrite <- app_assoc in EXEC. apply compiled_expr_not_incorrect_cont in EXEC as STEP1.
    destruct STEP1 as [n [EVAL1 COMP1]]. inversion COMP1. subst.
    exists st. exists i. exists (n :: o). auto.
  - simpl in EXEC.
    exists st. exists i. exists o. auto.
  - simpl in EXEC. rewrite <- app_assoc in EXEC.
    apply IHSp1 in EXEC as STEP1. destruct STEP1 as [st' [i' [o' [EVAL1 SSTEP1]]]].
    apply IHSp2 in SSTEP1 as STEP2. destruct STEP2 as [st'' [i'' [o'' [EVAL2 SSTEP2]]]].
    exists st''. exists i''. exists o''. split; auto.
    apply bs_Seq with (c' := (st', i', o')); auto.
  Qed.

  Lemma compiled_straightline_not_incorrect
        (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z)
        (EXEC : ([], st, i, o) -- compile p Sp --> ([], st', i', o')) :
    (st, i, o) == p ==> (st', i', o').
  Proof. replace (compile p Sp) with (compile p Sp ++ []) in EXEC by apply app_nil_r.
  apply compiled_straightline_not_incorrect_cont in EXEC as CONT.
  destruct CONT as [stm [im [om [EVALm STEPm]]]]. inversion STEPm. subst. auto.
  Qed.

  Theorem straightline_compiler_correct
          (p : stmt) (Sp : StraightLine p) (st st' : state Z) (i o i' o' : list Z) :
    (st, i, o) == p ==> (st', i', o') <-> ([], st, i, o) -- compile p Sp --> ([], st', i', o').
  Proof. split; intros.
  - apply compiled_straightline_correct. auto.
  - apply compiled_straightline_not_incorrect with (Sp := Sp). auto.
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
Proof. generalize dependent q. induction p; intros.
- simpl. rewrite Hocc. reflexivity.
- replace ((a :: p) ++ [JMP l]) with (a :: (p ++ [JMP l])) by auto.
  inversion Hwf. apply Bool.andb_true_iff in H0. destruct H0.
  assert (prog_wf_rec q (p ++ [JMP l]) = true) by auto.
  destruct a;
  simpl;
  (f_equal + (* nop *) auto);
  rewrite H0; rewrite H1; reflexivity.
Qed.

(* Generalized version of the same lemma *)
Ltac wf_app_helper p ins Hwf :=
induction p as [ | hp tp IHp];
try (simpl; subst; rewrite Bool.andb_true_r);
auto;
inversion Hwf as [H0]; apply Bool.andb_true_iff in H0; destruct H0 as [H1 H2];
apply IHp in H2 as HStep;
destruct hp; simpl; (f_equal + auto); rewrite H2; rewrite HStep; reflexivity.

Lemma wf_app_j (p q: prog) (l: nat) (ins: insn) (Hwf: prog_wf_rec q p = true)
    (Hocc: label_occurs_once l q = true)
    (INS: ins = JMP l \/ ins = JZ l \/ ins = JNZ l):
  prog_wf_rec q (p ++ [ins]) = true.
Proof. destruct INS as [JINS | [JINS | JINS]].
- wf_app_helper p (JMP l) Hwf.
- wf_app_helper p (JZ l) Hwf.
- wf_app_helper p (JNZ l) Hwf.
Qed.

Lemma wf_app_other (p q: prog) (ins: insn) (Hwf: prog_wf_rec q p = true)
    (INS: (exists lb, ins = LAB lb) \/ (exists sl, ins = B sl)):
  prog_wf_rec q (p ++ [ins]) = true.
Proof. destruct INS as [[lb] | [sl]]; subst.
- wf_app_helper p (LAB lb) Hwf.
- wf_app_helper p (B sl) Hwf.
Qed.

Lemma wf_rev (p q : prog) (Hwf : prog_wf_rec q p = true) : prog_wf_rec q (rev p) = true.
Proof. induction p.
- simpl. reflexivity.
- simpl. inversion Hwf. apply Bool.andb_true_iff in H0. destruct H0. destruct a.
  + rewrite H. rewrite H0. simpl. apply wf_app_j with (l := n); auto.
  + rewrite H. rewrite H0. simpl. apply wf_app_j with (l := n); auto.
  + rewrite H. rewrite H0. simpl. apply wf_app_j with (l := n); auto.
  + rewrite H0. simpl. apply wf_app_other; auto. left. exists n. auto.
  + rewrite H0. simpl. apply wf_app_other; auto. right. exists i. auto.
Qed.

Fixpoint convert_straightline (p : StraightLine.prog) : prog :=
  match p with
    []      => []
  | i :: p' => B i :: convert_straightline p'
  end.

Lemma cons_comm_app (A : Type) (a : A) (l1 l2 : list A) : l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof. rewrite Renaming.cons_app. rewrite app_assoc. reflexivity. Qed.

Definition compile_expr (e : expr) : prog :=
  convert_straightline (StraightLine.compile_expr e).
