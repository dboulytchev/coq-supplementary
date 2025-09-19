Require Import List.
Import ListNotations.
Require Import Lia.

Require Import BinInt ZArith_dec Zorder ZArith.
Require Export Id.
Require Export State.
Require Export Expr.

From hahn Require Import HahnBase.
Require Import Coq.Program.Equality.

(* AST for statements *)
Inductive stmt : Type :=
| SKIP  : stmt
| Assn  : id -> expr -> stmt
| READ  : id -> stmt
| WRITE : expr -> stmt
| Seq   : stmt -> stmt -> stmt
| If    : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf := (state Z * list Z * list Z)%type.

(* Big-step evaluation relation *)
Reserved Notation "c1 '==' s '==>' c2" (at level 0).

Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
| bs_Skip        : forall (c : conf), c == SKIP ==> c 
| bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
                          (s, i, o) == x ::= e ==> (s [x <- z], i, o)
| bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                          (s, z::i, o) == READ x ==> (s [x <- z], i, o)
| bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                          (VAL : [| e |] s => z),
                          (s, i, o) == WRITE e ==> (s, i, z::o)
| bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt)
                          (STEP1 : c == s1 ==> c') (STEP2 : c' == s2 ==> c''),
                          c ==  s1 ;; s2 ==> c''
| bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                          (CVAL : [| e |] s => Z.one)
                          (STEP : (s, i, o) == s1 ==> c'),
                          (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt)
                          (CVAL : [| e |] s => Z.zero)
                          (STEP : (s, i, o) == s2 ==> c'),
                          (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
| bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt)
                          (CVAL  : [| e |] st => Z.one)
                          (STEP  : (st, i, o) == s ==> c')
                          (WSTEP : c' == WHILE e DO s END ==> c''),
                          (st, i, o) == WHILE e DO s END ==> c''
| bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt)
                          (CVAL : [| e |] st => Z.zero),
                          (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

#[export] Hint Constructors bs_int : core.

(* "Surface" semantics *)
Definition eval (s : stmt) (i o : list Z) : Prop :=
  exists st, ([], i, []) == s ==> (st, [], o).

Notation "<| s |> i => o" := (eval s i o) (at level 0).

(* "Surface" equivalence *)
Definition eval_equivalent (s1 s2 : stmt) : Prop :=
  forall (i o : list Z),  <| s1 |> i => o <-> <| s2 |> i => o.

Notation "s1 ~e~ s2" := (eval_equivalent s1 s2) (at level 0).
 
(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Definition contextual_equivalent (s1 s2 : stmt) :=
  forall (C : Context), (C <~ s1) ~e~ (C <~ s2).

Notation "s1 '~c~' s2" := (contextual_equivalent s1 s2) (at level 42, no associativity).

Lemma contextual_equiv_stronger (s1 s2 : stmt) (H: s1 ~c~ s2) : s1 ~e~ s2.
Proof.
unfold contextual_equivalent in H.
unfold "~e~".
intros.
unfold eval_equivalent in H.
apply H with (C:= Hole).
Qed.

Lemma eval_equiv_weaker : exists (s1 s2 : stmt), s1 ~e~ s2 /\ ~ (s1 ~c~ s2).
Proof.
exists (Id 0 ::= Nat 0). 
exists (Id 0 ::= Nat 1).
split.
unfold eval_equivalent.
intros.
split; intros;
inversion H;
inversion H0; subst;
econstructor;
econstructor;
inversion VAL; subst;
econstructor.
unfold not. intros.
unfold "~c~" in H.
specialize (H (SeqL Hole (WRITE (Var (Id 0)))) nil ([0%Z])).
simpl in H.
assert (trueKent : (eval ((Id 0 ::= Nat 0);; WRITE (Var (Id 0))) nil ([0%Z]))).
exists [(Id 0, 0%Z)].
econstructor.
econstructor.
eauto.
econstructor.
econstructor.
econstructor.
apply H in trueKent.
destruct trueKent.
inversion H0; subst.
inversion STEP1; subst.
inversion STEP2; subst.
inversion VAL0; subst.
inversion VAL; subst.
inversion VAL0; subst.
inversion VAR0; subst.
contradiction.
Qed.



(* Big step equivalence *)
Definition bs_equivalent (s1 s2 : stmt) :=
  forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c'.

Notation "s1 '~~~' s2" := (bs_equivalent s1 s2) (at level 0).

Ltac seq_inversion :=
  match goal with
    H: _ == _ ;; _ ==> _ |- _ => inversion_clear H
  end.

Ltac seq_apply :=
  match goal with
  | H: _   == ?s1 ==> ?c' |- _ == (?s1 ;; _) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  | H: ?c' == ?s2 ==>  _  |- _ == (_ ;; ?s2) ==> _ => 
    apply bs_Seq with c'; solve [seq_apply | assumption]
  end.

Module SmokeTest.

  (* Associativity of sequential composition *)
  Lemma seq_assoc (s1 s2 s3 : stmt) :
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof.
  split; intros;
  seq_inversion;
  seq_inversion;
  seq_apply.
  Qed.
  
  (* One-step unfolding *)
  Lemma while_unfolds (e : expr) (s : stmt) :
    (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof.
   split; intros.
    - inversion_clear H; eauto.
    - inversion_clear H;
    inversion_clear STEP; eauto.
  Qed.
      
  (* Terminating loop invariant *)
  Lemma while_false (e : expr) (s : stmt) (st : state Z)
        (i o : list Z) (c : conf)
        (EXE : c == WHILE e DO s END ==> (st, i, o)) :
    [| e |] st => Z.zero.
  Proof.

    remember (WHILE e DO s END).
    
    remember ((st, i, o)).
    induction EXE; subst; try discriminate.
    - apply IHEXE2; eauto. 
    -
    inversion Heqp. subst.
    inversion Heqs0. subst. 
    auto.  
  Qed.
  
  (* Big-step semantics does not distinguish non-termination from stuckness *)
  Lemma loop_eq_undefined :
    (WHILE (Nat 1) DO SKIP END) ~~~
    (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof.
  unfold bs_equivalent;intros.
  split;intros.
  -
  inversion_clear H. inversion STEP.
  destruct c' eqn:E. destruct p.
  apply (while_false (Nat 1) SKIP s l0 l c'0) in WSTEP.
  inversion WSTEP. inversion CVAL.
  - 
  inversion_clear H; subst; try discriminate;
  inversion_clear CVAL; subst.
  Qed.  
  
  (* Loops with equivalent bodies are equivalent *)
  Lemma while_eq (e : expr) (s1 s2 : stmt)
        (EQ : s1 ~~~ s2) :
    WHILE e DO s1 END ~~~ WHILE e DO s2 END.
  Proof.
    unfold bs_equivalent. intros c c'.
    split; intro;
    dependent induction H;
    eauto;
    try (econstructor);
    eauto;
    try (apply EQ; eauto).
  Qed.  


  (* Loops with the constant true condition don't terminate *)
  (* Exercise 4.8 from Winskel's *)
  Lemma while_true_undefined c s c' :
    ~ c == WHILE (Nat 1) DO s END ==> c'.
  Proof.
  unfold not.
  intros.
  dependent induction H.
  -
  pose (IHbs_int2 s) as a1.
  apply a1.
  reflexivity.
  - inversion CVAL.
  Qed.

  
End SmokeTest.

(* Semantic equivalence is a congruence *)
Lemma eq_congruence_seq_r (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s  ;; s1) ~~~ (s  ;; s2).
Proof.
  unfold bs_equivalent.
  intros.
  split; intros;
  inversion H; subst;
  seq_inversion;
  econstructor;
  eauto;
  apply EQ; eauto.
Qed.


Ltac solve_bs_eq :=
  try (eauto; fail);  (* Сначала пробуем eauto *)
  match goal with
  | [ EQ : ?s1 ~~~ ?s2 |- _ ] =>
      try (apply EQ; eauto; fail);  (* Пробуем применить эквивалентность *)
      try (eauto using EQ; fail)    (* Пробуем использовать EQ в eauto *)
  end;
  try (constructor; eauto; fail).  (* Пробуем конструкторы с eauto *)

Lemma bs_eq_symm (s1 s2 : stmt) : (s1) ~~~ (s2) <-> (s2) ~~~ (s1).
Proof.
  split;intros;
  unfold bs_equivalent in *;
  intros;symmetry; eauto.
Qed.

Ltac bs_auto :=
  eauto;
  repeat (try (progress seq_inversion));
  try solve [econstructor; eauto];
  try  (
    match goal with
    | [ EQ : ?s1 ~~~ ?s2 |- _ ] =>
        pose proof (proj1 (bs_eq_symm s1 s2) EQ)
    end
  );
  try solve [
    match goal with
    | [ EQ : ?s1 ~~~ ?s2 |- _ ] =>
        first [apply EQ; eauto | eapply EQ; eauto]
    end
  ];
  eauto.



Ltac try_build :=
  bs_auto;
  repeat (try (progress seq_inversion));
  try solve [econstructor;bs_auto];
  try (eapply bs_If_True;bs_auto);
  try (eapply bs_If_False;bs_auto);
  try (eapply bs_While_True;bs_auto);
  try (eapply bs_While_False;bs_auto).

(* Ltac buid_w_inv := *)
  

Lemma eq_congruence_seq_l (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  (s1 ;; s) ~~~ (s2 ;; s).
Proof.
  unfold bs_equivalent.
  intros.
  split; intros;
  inversion H; subst;
  (* seq_inversion; *)
  try_build.
Qed.


Lemma eq_congruence_cond_else
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END.
Proof.

unfold bs_equivalent. 
intros.
  split; intros.
  - dependent destruction H;
    try_build.
  - dependent destruction H;
    try_build.
Qed.


Lemma eq_congruence_cond_then
      (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  COND e THEN s1 ELSE s END ~~~ COND e THEN s2 ELSE s END.
Proof.
  unfold bs_equivalent.
  intros.
  split; intros.
  try_build.
  - dependent destruction H;
    try_build.
  - dependent destruction H;
  try_build.
Qed.

Lemma eq_congruence_while
      (e : expr) (s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof.
unfold bs_equivalent. 
intros.
  split; intros.
  - dependent destruction H;  
    try_build.
    eapply SmokeTest.while_eq with (s2:=s1); eauto.
  - dependent destruction H;
    try_build.
    eapply SmokeTest.while_eq with (s1:=s2); eauto.
Qed.


Lemma eq_congruence (e : expr) (s s1 s2 : stmt) (EQ : s1 ~~~ s2) :
  ((s  ;; s1) ~~~ (s  ;; s2)) /\
  ((s1 ;; s ) ~~~ (s2 ;; s )) /\
  (COND e THEN s  ELSE s1 END ~~~ COND e THEN s  ELSE s2 END) /\
  (COND e THEN s1 ELSE s  END ~~~ COND e THEN s2 ELSE s  END) /\
  (WHILE e DO s1 END ~~~ WHILE e DO s2 END).
Proof.
split;
try_build;
split;
intros;
try_build;
split;
try split;
intros;
try_build;
unfold bs_equivalent; intros;
try split; intros.
try_build.
-
try solve
[eapply eq_congruence_cond_else;
try_build].
-
eapply eq_congruence_cond_else;
try_build.
-
eapply eq_congruence_cond_then;
try_build.
-
eapply eq_congruence_cond_then;
try_build.
-
eapply eq_congruence_while;
try_build.
-
eapply eq_congruence_while;
try_build.
Qed.

(* Big-step semantics is deterministic *)
Ltac by_eval_deterministic :=
  match goal with
    H1: [|?e|]?s => ?z1, H2: [|?e|]?s => ?z2 |- _ => 
     apply (eval_deterministic e s z1 z2) in H1; [subst z2; reflexivity | assumption]
  end.

Ltac eval_zero_not_one :=
  match goal with
    H : [|?e|] ?st => (Z.one), H' : [|?e|] ?st => (Z.zero) |- _ =>
    assert (Z.zero = Z.one) as JJ; [ | inversion JJ];
    eapply eval_deterministic; eauto
  end.



Lemma bs_int_deterministic (c c1 c2 : conf) (s : stmt)
    (EXEC1 : c == s ==> c1) (EXEC2 : c == s ==> c2) :
c1 = c2.
Proof.
generalize dependent c1.
induction EXEC2; intros;
inversion EXEC1; subst; eauto;
try by_eval_deterministic; subst; try_build;
try eval_zero_not_one.
-
specialize (IHEXEC2_1 c'0 STEP1).
subst.
specialize (IHEXEC2_2 c1 STEP2).
assumption.
-
specialize (IHEXEC2_1 c'0 STEP).
subst.
specialize (IHEXEC2_2 c1 WSTEP).
assumption.
Qed.


Definition equivalent_states (s1 s2 : state Z) :=
  forall id, Expr.equivalent_states s1 s2 id.

Lemma update_lol 
(st1 st1' : state Z)
(x : id)
(z : Z)
 
(HH : equivalent_states st1 st1')
:
(equivalent_states (st1) [x <- z] (st1') [x <- z]).
Proof.
unfold equivalent_states in *.
intro.
unfold Expr.equivalent_states in *.
intro.
rewrite st_eqiv.
rewrite st_eqiv.
specialize (HH id z0).
rewrite st_eqiv in HH.
rewrite st_eqiv in HH.
split; intros; inversion H; subst;
destruct (id_eq_dec x id);
redu; subst; inversion H1; subst;
try rewrite <- H;
unfold update in *; simpl;
redu; eauto;
redu.
symmetry.
apply HH in H1; congruence.
apply HH in H1; congruence.
Qed.



Lemma eqeqeq (s1 s2 : state Z)
  (HE1 : equivalent_states s1 s2)
  (e : expr) (z : Z)
  (H : [|e|] s1 => z) : [|e|] s2 => z.
Proof.
  induction H; intros; try constructor; eauto.
  apply HE1. auto.
Qed.


Ltac addeval :=
  match goal with
    VAL: [|?e|]?st1 => ?z, HE1 : equivalent_states ?st1 ?st1' |- _ => 
  pose (eqeqeq _ _ HE1 _ _ VAL)
  end.

(* Ltac add_obv :=
  match goal with
    VAL: (?a = ?a) -> _ |- _ => 
  (* assert (eqty : (st1, i, o) = (st1, i, o)). { reflexivity. } *)
    pose (eqeqeq _ _ HE1 _ _ VAL)
  end.
 *)
Ltac add_obv :=
  match goal with
  | [ VAL : (?a = ?a) -> _ |- _ ] =>
      let H := fresh "H" in
      assert (H : a = a) by reflexivity;
      specialize (VAL H);
      clear H
  end.


Ltac solve_bsint :=
  match goal with
  | [IHbs_int : forall (i o i'0 o'0 : list Z)
    (st3 st4 st1' : state Z),
    equivalent_states ?st3 ?st1' ->
    (?st1, ?i0, ?o0) = (?st3, ?i, ?o) ->
    (?st2, ?i', ?o') = (?st4, ?i'0, ?o'0) -> _ , 
    HE1 : equivalent_states ?st1 ?st1'
|- _] =>
    pose (IHbs_int i0 o0 i' o' st1 st2 st1') as kk;
    specialize (kk HE1);
    add_obv;
    add_obv
end.

Ltac solve_bsint2 :=
  match goal with
  | [IHbs_int : ?i -> ?o -> ?i'0 -> ?o'0 -> 
    ?st3 -> ?st4 -> ?st1' ->
    equivalent_states ?st3 ?st1' ->
    (?st1, ?i0, ?o0) = (?st3, ?i, ?o) ->
    (?st2, ?i', ?o') = (?st4, ?i'0, ?o'0) -> _ , 
    HE1 : equivalent_states ?st1 ?st1'
|- _] =>
    pose (IHbs_int i0 o0 i' o' st1 st2 st1') as kk;
    specialize (kk HE1);
    add_obv;
    add_obv
end.

Ltac solve_bsint3 :=
  match goal with
  | [ IH : forall (i o i'0 o'0 : list Z)
               (st3 st4 st1' : state Z),
        equivalent_states st3 st1' ->
        (?st1, ?i0, ?o0) = (st3, i, o) ->
        (?st2, ?i', ?o') = (st4, i'0, o'0) -> _ ,
      HE1 : equivalent_states ?st1 ?st1' 
    |- _ ] =>
    pose (IH i0 o0 i' o' st1 st2 st1') as kk;
    specialize (kk HE1);
    add_obv;
    add_obv;
    destruct kk as [x H4];
    destruct H4;
    clear IH
  
end.

Ltac solve_bsint4 :=
  match goal with
  | [ IH : forall (i o i'0 o'0 : list Z)
               (st1 st3 st1' : state Z),
        equivalent_states st1 st1' ->
        (?s0, ?l0, ?l) = (st1, i, o) ->
        (?st2, ?i', ?o') = (st3, i'0, o'0) -> _ ,
      HE1 : equivalent_states ?s0 ?x 
    |- _ ] =>
    pose (IH l0 l i' o' s0 st2 x ) as rkk;
    specialize (rkk HE1);
    add_obv;
    add_obv;
    destruct rkk as [rr rH4];
    destruct rH4;
    clear IH
  
end.

Lemma bs_equiv_states
  (s            : stmt)
  (i o i' o'    : list Z)
  (st1 st2 st1' : state Z)
  (HE1          : equivalent_states st1 st1')  
  (H            : (st1, i, o) == s ==> (st2, i', o')) :
  exists st2',  equivalent_states st2 st2' /\ (st1', i, o) == s ==> (st2', i', o').
Proof.

remember (st1, i, o). remember (st2, i', o'). 
generalize i o i' o' st1 st2 st1' HE1 Heqp Heqp0. 
  clear Heqp0 Heqp HE1 st1' st2 st1 o' i' o i. 
  dependent induction H; intros;
  try solve [subst; inversion Heqp0; subst; exists st1'; split; eauto];
  inversion Heqp; inversion Heqp0; subst.
  - exists (st1' [x <- z]). split.  
  + apply update_lol. eauto. 
  + econstructor. eapply eqeqeq; eauto.
  - exists (st1' [x <- z]). split; 
    try apply update_lol; eauto.
  - exists st1'. split. eauto.
    econstructor. eapply eqeqeq; eauto.
    - destruct c' , p; auto.
    solve_bsint3.
    solve_bsint4.
    exists rr. split. 
    + eauto. 
    + seq_apply.
  -
  solve_bsint3.
    exists x. split. auto. 
    econstructor; try eapply eqeqeq; eauto.
  - solve_bsint3.
  exists x. split. apply H1. apply bs_If_False; try eapply eqeqeq; eauto.
  - destruct c' , p. 
  solve_bsint3.
  solve_bsint4.
    exists rr. split. eauto. econstructor; 
    try eapply eqeqeq; eauto.
  - exists st1'. split. apply HE1. apply bs_While_False. eapply eqeqeq; eauto.
Qed.
  
(* Contextual equivalence is equivalent to the semantic one *)
(* TODO: no longer needed *)
Ltac by_eq_congruence e s s1 s2 H :=
  remember (eq_congruence e s s1 s2 H) as Congruence;
  match goal with H: Congruence = _ |- _ => clear H end;
  repeat (match goal with H: _ /\ _ |- _ => inversion_clear H end); assumption.
      
(* Small-step semantics *)
Module SmallStep.
  
  Reserved Notation "c1 '--' s '-->' c2" (at level 0).

  Inductive ss_int_step : stmt -> conf -> option stmt * conf -> Prop :=
  | ss_Skip        : forall (c : conf), c -- SKIP --> (None, c) 
  | ss_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z) 
                            (SVAL : [| e |] s => z),
      (s, i, o) -- x ::= e --> (None, (s [x <- z], i, o))
  | ss_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
      (s, z::i, o) -- READ x --> (None, (s [x <- z], i, o))
  | ss_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z)
                            (SVAL : [| e |] s => z),
      (s, i, o) -- WRITE e --> (None, (s, i, z::o))
  | ss_Seq_Compl   : forall (c c' : conf) (s1 s2 : stmt)
                            (SSTEP : c -- s1 --> (None, c')),
      c -- s1 ;; s2 --> (Some s2, c')
  | ss_Seq_InCompl : forall (c c' : conf) (s1 s2 s1' : stmt)
                            (SSTEP : c -- s1 --> (Some s1', c')),
      c -- s1 ;; s2 --> (Some (s1' ;; s2), c')
  | ss_If_True     : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.one),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s1, (s, i, o))
  | ss_If_False    : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr)
                            (SCVAL : [| e |] s => Z.zero),
      (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s2, (s, i, o))
  | ss_While       : forall (c : conf) (s : stmt) (e : expr),
      c -- WHILE e DO s END --> (Some (COND e THEN s ;; WHILE e DO s END ELSE SKIP END), c)
  where "c1 -- s --> c2" := (ss_int_step s c1 c2).

  Reserved Notation "c1 '--' s '-->>' c2" (at level 0).

  Inductive ss_int : stmt -> conf -> conf -> Prop :=
    ss_int_Base : forall (s : stmt) (c c' : conf),
                    c -- s --> (None, c') -> c -- s -->> c'
  | ss_int_Step : forall (s s' : stmt) (c c' c'' : conf),
                    c -- s --> (Some s', c') -> c' -- s' -->> c'' -> c -- s -->> c'' 
  where "c1 -- s -->> c2" := (ss_int s c1 c2).

  Lemma ss_int_step_deterministic (s : stmt)
        (c : conf) (c' c'' : option stmt * conf) 
        (EXEC1 : c -- s --> c')
        (EXEC2 : c -- s --> c'') :
    c' = c''.
  Proof.
    dependent induction s;
    dependent destruction EXEC1; dependent destruction EXEC2;
    try by_eval_deterministic;
    try eval_zero_not_one; eauto;
    specialize (IHs1 _ _ _ EXEC1 EXEC2); inversion IHs1; subst; eauto.
  Qed.
  
  Lemma ss_int_deterministic (c c' c'' : conf) (s : stmt)
        (STEP1 : c -- s -->> c') (STEP2 : c -- s -->> c'') :
    c' = c''.
  Proof.
  generalize dependent c''.
  induction STEP1; intros; inversion STEP2; subst; eauto;
  try remember (ss_int_step_deterministic s c _ _ H H0) as H2;
  try remember (ss_int_step_deterministic _ _ _ _ H H0) as H2; 
  inversion H2; eauto; try discriminate H2; subst.
  specialize (IHSTEP1 c''0). specialize (IHSTEP1 H1). assumption.
  Qed.

  
  Lemma ss_bs_base (s : stmt) (c c' : conf) (STEP : c -- s --> (None, c')) :
    c == s ==> c'.
  Proof.
  inversion STEP; subst; auto.
  Qed.

  Lemma ss_ss_composition (c c' c'' : conf) (s1 s2 : stmt)
        (STEP1 : c -- s1 -->> c'') (STEP2 : c'' -- s2 -->> c') :
    c -- s1 ;; s2 -->> c'. 
  Proof.
  dependent induction STEP1; intros.
  apply (ss_int_Step _ s2 _ c'0).
  constructor; eauto.
  eauto.  
  eapply (ss_int_Step _ (s';; s2) _ c'0);
  specialize (IHSTEP1 STEP2).
  constructor;eauto.
  eauto.
  Qed.  
  
  Lemma ss_bs_step (c c' c'' : conf) (s s' : stmt)
        (STEP : c -- s --> (Some s', c'))
        (EXEC : c' == s' ==> c'') :
    c == s ==> c''.
  Proof.
    generalize dependent c''.
    generalize dependent s'.
    generalize dependent c'.
    dependent induction s; intros; inversion STEP; subst.
    - apply bs_Seq with c'.
      apply ss_bs_base. eauto. eauto.
    - inversion EXEC; subst; try_build.
    - try_build.
    - try_build.
    - inversion EXEC; subst;
      inversion STEP0; subst; try_build.
  Qed.
  
  Theorem bs_ss_eq (s : stmt) (c c' : conf) :
    c == s ==> c' <-> c -- s -->> c'.
  Proof.
      split; intros.
      - dependent induction s;
      try  solve [constructor; dependent destruction H; econstructor; eauto ].
      dependent induction H. eapply ss_ss_composition; eauto.
      dependent destruction H. try_build. try_build.  
      dependent induction H.  
        * eapply ss_int_Step. 
          try_build.
          eapply ss_int_Step. try_build. 
          eapply ss_ss_composition. apply IHs. eassumption. eauto.
        * eapply ss_int_Step.
          try_build. 
          eapply ss_int_Step. try_build.  
          constructor. constructor. 
      - dependent induction H.
        apply ss_bs_base. eauto.
        eapply ss_bs_step; eauto.
  Qed.  
  
End SmallStep.

Module Renaming.

  Definition renaming := Renaming.renaming.

  Definition rename_conf (r : renaming) (c : conf) : conf :=
    match c with
    | (st, i, o) => (Renaming.rename_state r st, i, o)
    end.
  
  Fixpoint rename (r : renaming) (s : stmt) : stmt :=
    match s with
    | SKIP                       => SKIP
    | x ::= e                    => (Renaming.rename_id r x) ::= Renaming.rename_expr r e
    | READ x                     => READ (Renaming.rename_id r x)
    | WRITE e                    => WRITE (Renaming.rename_expr r e)
    | s1 ;; s2                   => (rename r s1) ;; (rename r s2)
    | COND e THEN s1 ELSE s2 END => COND (Renaming.rename_expr r e) THEN (rename r s1) ELSE (rename r s2) END
    | WHILE e DO s END           => WHILE (Renaming.rename_expr r e) DO (rename r s) END             
    end.   

  Lemma re_rename
    (r r' : Renaming.renaming)
    (Hinv : Renaming.renamings_inv r r')
    (s    : stmt) : rename r (rename r' s) = s.
  Proof.
    induction s; simpl; eauto;
    try rewrite (Renaming.re_rename_expr r r' Hinv e); eauto;
    try rewrite (Hinv i);
    eauto;
    try rewrite IHs1, IHs2; eauto.
    rewrite IHs.
    eauto.
  Qed.
  
  Lemma rename_state_update_permute (st : state Z) (r : renaming) (x : id) (z : Z) :
    Renaming.rename_state r (st [ x <- z ]) = (Renaming.rename_state r st) [(Renaming.rename_id r x) <- z].
  Proof.
    unfold update.
    simpl.
    destruct r.
    eauto.
  Qed. 
  
  #[export] Hint Resolve Renaming.eval_renaming_invariance : core.

  Lemma renaming_invariant_bs
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : c == s ==> c') : (rename_conf r c) == rename r s ==> (rename_conf r c').
  Proof.
    destruct r.
    induction Hbs; subst; simpl;eauto;
    try (constructor;
      apply Renaming.eval_renaming_invariance;eauto).
    eapply bs_If_True;
      try apply Renaming.eval_renaming_invariance; eauto.
    eapply bs_If_False;
      try apply Renaming.eval_renaming_invariance; eauto.
    eapply bs_While_True;
      try apply Renaming.eval_renaming_invariance; eauto.
  Qed.    
  
  Lemma renaming_invariant_bs_inv
    (s         : stmt)
    (r         : Renaming.renaming)
    (c c'      : conf)
    (Hbs       : (rename_conf r c) == rename r s ==> (rename_conf r c')) : c == s ==> c'.
  Proof.
    remember (Renaming.renaming_inv r) as r'.
    inversion r'.
    apply renaming_invariant_bs with (r:=x) in Hbs.
    assert (KK : forall c2,  rename_conf x (rename_conf r c2) = c2).
    {intro c2.
    destruct c2, p. simpl.
    rewrite Renaming.re_rename_state; eauto. }
    rewrite re_rename in Hbs;
    rewrite KK in Hbs;
    rewrite KK in Hbs;
    eauto.
  Qed.
    
  Lemma renaming_invariant (s : stmt) (r : renaming) : s ~e~ (rename r s).
  Proof.
    unfold eval_equivalent, eval in *.
    split; intros; destruct H.
    - exists (Renaming.rename_state r x). 
      apply (renaming_invariant_bs _ _ _ _ H).
    - pose (Renaming.renaming_inv2 r) as e.
      destruct e.
      assert (KK : forall c2,  rename_conf r (rename_conf x0 c2) = c2).
      {intro c2.
      destruct c2, p. simpl.
      rewrite Renaming.re_rename_state; eauto. }
      rewrite <- KK in H.
      apply (renaming_invariant_bs_inv _ _ ([], i, [])) in H.
      simpl in H.
      exists (Renaming.rename_state x0 x).
      eauto. 
  Qed.
  
End Renaming.

(* CPS semantics *)
Inductive cont : Type := 
| KEmpty : cont
| KStmt  : stmt -> cont.
 
Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont)
                           (CSTEP : KEmpty |- c -- k --> c'),
    k |- c -- !SKIP --> c'
| cps_Assign      : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (e : expr) (n : Z)
                           (CVAL : [| e |] s => n)
                           (CSTEP : KEmpty |- (s [x <- n], i, o) -- k --> c'),
    k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (x : id) (z : Z)
                           (CSTEP : KEmpty |- (s [x <- z], i, o) -- k --> c'),
    k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (z : Z)
                           (CVAL : [| e |] s => z)
                           (CSTEP : KEmpty |- (s, i, z::o) -- k --> c'),
    k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt)
                           (CSTEP : !s2 @ k |- c -- !s1 --> c'),
    k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                           (CVAL : [| e |] s => Z.one)
                           (CSTEP : k |- (s, i, o) -- !s1 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s1 s2 : stmt)
                           (CVAL : [| e |] s => Z.zero)
                           (CSTEP : k |- (s, i, o) -- !s2 --> c'),
    k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                           (CVAL : [| e |] st => Z.one)
                           (CSTEP : !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf)
                           (k : cont) (e : expr) (s : stmt)
                           (CVAL : [| e |] st => Z.zero)
                           (CSTEP : KEmpty |- (st, i, o) -- k --> c'),
    k |- (st, i, o) -- !(WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Ltac cps_bs_gen_helper k H HH :=
  destruct k eqn:K; subst; inversion H; subst;
  [inversion EXEC; subst | eapply bs_Seq; eauto];
  apply HH; auto.
    
Lemma cps_bs_gen (S : stmt) (c c' : conf) (S1 k : cont)
      (EXEC : k |- c -- S1 --> c') (DEF : !S = S1 @ k):
  c == S ==> c'.
Proof. admit. Admitted.

Lemma cps_bs (s1 s2 : stmt) (c c' : conf) (STEP : !s2 |- c -- !s1 --> c'):
   c == s1 ;; s2 ==> c'.
Proof. admit. Admitted.

Lemma cps_int_to_bs_int (c c' : conf) (s : stmt)
      (STEP : KEmpty |- c -- !(s) --> c') : 
  c == s ==> c'.
Proof. admit. Admitted.

Lemma cps_cont_to_seq c1 c2 k1 k2 k3
      (STEP : (k2 @ k3 |- c1 -- k1 --> c2)) :
  (k3 |- c1 -- k1 @ k2 --> c2).
Proof. admit. Admitted.

Lemma bs_int_to_cps_int_cont c1 c2 c3 s k
      (EXEC : c1 == s ==> c2)
      (STEP : k |- c2 -- !(SKIP) --> c3) :
  k |- c1 -- !(s) --> c3.
Proof. admit. Admitted.

Lemma bs_int_to_cps_int st i o c' s (EXEC : (st, i, o) == s ==> c') :
  KEmpty |- (st, i, o) -- !s --> c'.
Proof. admit. Admitted.

(* Lemma cps_stmt_assoc s1 s2 s3 s (c c' : conf) : *)
(*   (! (s1 ;; s2 ;; s3)) |- c -- ! (s) --> (c') <-> *)
(*   (! ((s1 ;; s2) ;; s3)) |- c -- ! (s) --> (c'). *)
