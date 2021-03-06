(* CSE 505 Programming Languages
   Homework 2
   Due: Friday, Oct 23

   Total points for Coq part: 100

   HW 2 requires you to write your own inductive definitions,
   theorems, and proofs. We encourage you to get started early!
*)

Require Import List.
Import ListNotations.
Require Import String.
Require Import ZArith.

Open Scope string_scope.
(* This tactic will be useful in many of the following problems *)
Ltac break_match :=
  match goal with
    | _ : context [ if ?cond then _ else _ ] |- _ =>
     destruct cond as [] eqn:?
    | |- context [ if ?cond then _ else _ ] =>
      destruct cond as [] eqn:?
    | _ : context [ match ?cond with _ => _ end ] |- _ =>
     destruct cond as [] eqn:?
    | |- context [ match ?cond with _ => _ end ] =>
      destruct cond as [] eqn:?
  end.

(* Use break_match to automatically destruct the expression you're
    matching against in a match statement. This is especially useful 
    when the expression is complex:
 *)
Lemma break_match_example_1 :
  forall x y z,
    (match (3 * x + y * y + z) with
       | O => true
       | S _ => true
     end) = true.
Proof.
  intros. break_match; auto.
Qed.

(* break_match is also useful for getting rid of pesky let statements: *)
Lemma break_match_example_2 :
  forall p : nat * nat,
    (let (x, y) := p in x + y) = fst p + snd p.
Proof.
  intros. break_match. subst. simpl. reflexivity.
Qed.

(* This is necessary for annoying Coq reasons. *)
Notation length := List.length.

(* [PROBLEM 1 (5 points)]: Prove the following lemmas. 
   They will be useful in many of the problems below!
 *)

Lemma orb_false_intro :
  forall b1 b2,
    b1 = false ->
    b2 = false ->
    (orb b1 b2) = false.
Proof.
  intros. rewrite H; rewrite H0.
  simpl. reflexivity.
Qed.

Lemma orb_false_elim :
  forall b1 b2,
    (orb b1 b2) = false ->
    b1 = false /\ b2 = false.
Proof.
  intros.
  destruct b1.
  - simpl in H. inversion H.
  - simpl in *. rewrite H.
    split. reflexivity. reflexivity.
Qed.
  (* About 10 tactics *)

(* END PROBLEM 1 *)

(*
  We will extend IMP with the ability to push and pop heaps.

  In normal IMP, program states just included the heap "h" and
  statement to execute "s".

  In our extended version of IMP, program state will also include
  the current stack of heaps "l", represented as a list.

  There will be two new statements: "PushHeap" and "PopHeap x".
    - "PushHeap" adds the current heap "h" to the beginning of "l".
      Informally, it copies "h" all at once.
    - "PopHeap x" replaces the current heap "h" with the first
      element of "l" *except* "x" maps to "lkup x h" and replaces "l"
      with the tail of "l".  If "l" is the empty list, then
     "PopHeap x" has no effect.
  Both "PushHeap" and "PopHeap x" become Skip in one step.

  Note that there are some other differences from IMP as defined in
  class : Cond takes an "else" case and heaps are represented as lists
  instead of functions.

*)

Set Implicit Arguments.

Definition var := string.

(* We'll start by defining the syntax of our extended IMP. *)

(* Expressions are just like those from IMP seen in lecture. *)
Inductive Expr : Type :=
| Int : nat -> Expr
| Var : var -> Expr
| Add : Expr -> Expr -> Expr
| Mul : Expr -> Expr -> Expr.

(* [PROBLEM 2 (5 points)]
   Add the PushHeap and PopHeap x statements to the Stmt type. *)
Inductive Stmt : Type :=
| Skip : Stmt
| Assign : var -> Expr -> Stmt
| Seq : Stmt -> Stmt -> Stmt
| Cond : Expr -> Stmt -> Stmt -> Stmt
| While : Expr -> Stmt -> Stmt
| PushHeap: Stmt
| PopHeap: var -> Stmt
(*
  Add constructors for PushHeap and PopHeap x here. Remember:
    - "PushHeap" adds the current heap "h" to the beginning of "l".
      Informally, it copies "h" all at once.
    - "PopHeap x" replaces the current heap "h" with the first
      element of "l" *except* "x" maps to "lkup x h" and replaces "l"
      with the tail of "l".  If "l" is the empty list, then
      "PopHeap x" has no effect.
*)
.

(* END PROBLEM 2 *)

(* Next we define the semantics of our language *)

(* Heaps are represented as association lists. *)
Definition Heap := list (var * nat).

Fixpoint lkup (x: var) (h: Heap) :=
  match h with
    | nil => 0
    | (k, v) :: h' => if string_dec x k then v else lkup x h'
  end.

(* Since expressions are unchanged from IMP, their semantics are the same: *)
Inductive Eval : Heap -> Expr -> nat -> Prop :=
| EInt : forall h z,
  Eval h (Int z) z
| EVar : forall h v,
  Eval h (Var v) (lkup v h)
| EAdd : forall h e1 e2 c1 c2 c3,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  c3 = (c1 + c2) ->
  Eval h (Add e1 e2) c3
| EMul : forall h e1 e2 c1 c2 c3,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  c3 = (c1 * c2) ->
  Eval h (Mul e1 e2) c3.

(*
  [Problem 3 (5 points)]:
  Define a small-step operational semantics for our extended version of IMP.
  Include all the rules.
*)
Inductive Step : list Heap -> Heap -> Stmt ->
                 list Heap -> Heap -> Stmt -> Prop := 
| step_skip:
  forall hlist h s,
    Step hlist h (Seq Skip s) hlist h s
| step_assign:
  forall hlist h e v n,
    Eval h e n ->
    Step hlist h (Assign v e) hlist ((v,n)::h) Skip
| step_seq:
    forall hlist h s1 hlist' h' s1' s2,
      Step hlist h s1 hlist' h' s1'->
        Step hlist h (Seq s1 s2) hlist' h' (Seq s1' s2)
| step_cond_true:
    forall hlist h e s1 s2 n,
      Eval h e n ->
        n <> 0 ->
          Step hlist h (Cond e s1 s2) hlist h s1
| step_cond_false:
    forall hlist h e s1 s2 n,
      Eval h e n ->
        n = 0 ->
          Step hlist h (Cond e s1 s2) hlist h s2
| step_while_true:
    forall hlist h e s n,
      Eval h e n ->
        n <> 0 ->
          Step hlist h (While e s) hlist h (Seq s (While e s))
| step_while_false:
    forall hlist h e s n,
      Eval h e n ->
        n = 0 ->
          Step hlist h (While e s) hlist h Skip
| step_pushHeap:
    forall hlist h,
      Step hlist h PushHeap (h::hlist) h Skip
| step_popHeap_empty:
    forall h x,
      Step [] h (PopHeap x) [] h Skip
| step_popHeap_nonempty:
    forall h hlhead hltail x,
      Step (hlhead::hltail) h (PopHeap x) hltail ((x,lkup x h)::hlhead) Skip.

(*
  Add the rules (constructors) for the small step semantics of
  our extended version of IMP.  I have 10 rules in my solution.

  * NOTE *
  For statements that involve branching (Cond and While), the
  "then" / "enter loop" branch should be taken when the condition
  expression evaluates to something not equal to 0, and the
  "else" / "exit loop" branch should be taken when the condition
  expression evaluates to 0.
*)
(* END PROBLEM 3 *)

(*
  [PROBLEM 4 (5 points)]
  In a short English paragraph, explain why our language would be much less
  useful if popping a heap did not copy one value from the popped heap.

  Ans: If we just simply pop a heap without changing its value, we are just returning to 
  an old stage of the program when all new values in the current heap are not assigned.
  But if we copy a value from the currently heap, this means that we are actually we can have a
  'return value' from the most recent computation (computations between two heaps), and this allow
  us to implement sub-procedures in our program, where we can freely use original vairables without 
  worrying about breaking them, and we can get a return value by 'PopHeap retval' operation.
*)

(*
  [PROBLEM 5 (5 points)]
  Give an IMP program with a non-trivial use of PushHeap and PopHeap.
  
*)

Definition myProg := 
(Seq
  (Seq
    (Seq 
      (Assign "x" (Int 0))
      (Seq 
        (Assign "y" (Int 1)) 
        (Assign "n" (Int 10))
      )
    )
    PushHeap
  )
  (Seq
    (While (Var "n")
      (Seq
        (Assign "x0" (Add (Var "x") (Var "y")))
        (Seq
          (Assign "x" (Var "y"))
          (Seq
            (Assign "y" (Var "x0"))
            (Assign "n" (Int 0)) (*should be n = n-1, but there is no minus here*)
          )
        )
      )
    )
    (PopHeap "result")
  )
).

(* Interpreters *)

(*
  In class we saw how to implement and verify a function
  that evaluates expressions:
*)

Fixpoint eval (h: Heap) (e: Expr) : nat :=
  match e with
    | Int z => z
    | Var v => lkup v h
    | Add e1 e2 =>  (eval h e1) + (eval h e2)
    | Mul e1 e2 =>  (eval h e1) * (eval h e2)
  end.

Lemma eval_Eval:
  forall h e c,
  eval h e = c -> Eval h e c.
Proof.
  induction e; intros; simpl in *; subst; try constructor.
  - specialize (IHe1 (eval h e1)).
    specialize (IHe2 (eval h e2)).
    econstructor; eauto.
  - specialize (IHe1 (eval h e1)).
    specialize (IHe2 (eval h e2)).
    econstructor; eauto.
Qed.

Lemma Eval_eval:
  forall h e c,
  Eval h e c -> eval h e = c.
Proof.
  intros.
  induction H; subst; reflexivity.
Qed.

Lemma Eval_eval':
  forall h e,
  Eval h e (eval h e).
Proof.
  intros. remember (eval h e) as c. apply eval_Eval. omega.
Qed.


(* [Problem 6 (5 points)] *)
(* Implement step as a function. *)
(* Hint: Use eq_nat_dec to decide if two nats are equal. *)

Check eq_nat_dec.

Fixpoint step (hlist: list Heap) (h: Heap) (s: Stmt) :
  option (list Heap * Heap * Stmt) :=
  match s with
  | Skip => None
  | Assign v e =>
      Some (hlist, (v,(eval h e))::h, Skip)
  | Seq s1 s2 =>
      match (step hlist h s1) with
      | None => 
          Some (hlist, h, s2)
      | Some (hlist', h', s1')
          => Some (hlist', h', (Seq s1' s2))
      end
  | Cond e s1 s2 =>
      if eq_nat_dec (eval h e) 0 then
        Some (hlist, h, s2)
      else
        Some (hlist, h, s1)
  | While e s =>
      if eq_nat_dec (eval h e) 0 then
        Some(hlist, h, Skip)
      else
        Some (hlist, h, (Seq s (While e s)))
  | PushHeap =>
      Some (h::hlist, h, Skip)
  | PopHeap x =>
      match hlist with
      | [] => Some ([], h, Skip)
      | hd::htail => Some (htail, (x, lkup x h)::hd, Skip)
      end
  end.

(* END PROBLEM 6 *)

(* [Problem 7 (5 points)] *)
(* Prove that only Skip cannot step. *)
Lemma step_None_Skip:
  forall l h s, step l h s = None -> s = Skip.
Proof.
  intros. induction s.
  - intros. reflexivity.
  - intros. inversion H.
  - intros. inversion H.
    break_match. break_match. break_match. inversion H1.
    inversion H1.
  - simpl in *. break_match. inversion H. inversion H.
  - inversion H. break_match. 
    + inversion H1. 
    + inversion H1.
  - inversion H.
  - inversion H. break_match. inversion H1. inversion H1.
Qed.

(* About 15 tactics *)

(* END PROBLEM 7 *)

(* [Problem 8 (5 points)] *)
(* Prove that your step function is SOUND with respect to the Step relation. *)
Lemma step_Step:
  forall l h s l' h' s',
  step l h s = Some (l', h', s') -> Step l h s l' h' s'.
Proof.
  intros l h s. revert l; revert h.
  induction s.
  - intros. simpl in H. inversion H.
  - intros. simpl in *. inversion H. constructor. apply Eval_eval'.
  - intros. simpl in *.
    destruct (step l h s1) as [[[eqo_hl eqo_h] eqo_s]|] eqn:?.
    + inversion H. constructor.
      apply IHs1 in Heqo. subst.
      apply Heqo.
    + inversion H. subst. apply step_None_Skip in Heqo.
      subst. constructor.
  - intros. simpl in *.
    destruct (eq_nat_dec (eval h e) 0) in H.
    + inversion H. subst. eapply step_cond_false.
      eapply Eval_eval'. apply e0.
    + inversion H. subst. eapply step_cond_true.
      eapply Eval_eval'. apply n.
  - intros. simpl in *.
    destruct (eq_nat_dec (eval h e) 0) in H.
    + inversion H. subst. eapply step_while_false.
      eapply Eval_eval'. apply e0.
    + destruct (step l h s) as [[[eqo_hl eqo_h]]|] eqn:?.
      * inversion H; subst. apply IHs in Heqo.
        eapply step_while_true. apply Eval_eval'. apply n.
      * inversion H; subst. apply step_None_Skip in Heqo.
        subst. econstructor. apply Eval_eval'. apply n.
  - intros. inversion H; subst. constructor.
  - intros. inversion H.
    destruct l.
    + inversion H1; subst. constructor.
    + inversion H1; subst. constructor.
Qed.
(* END PROBLEM 8 *)

(* [Problem 9 (5 points)] *)
(* Prove that your step function is COMPLETE with respect to the Step relation. *)
Lemma Step_step:
  forall l h s l' h' s',
  Step l h s l' h' s' -> step l h s = Some (l', h', s').
Proof.
  intros l h s. revert l h.
  induction s.
  - intros. inversion H.
  - intros. inversion H; subst.
    simpl in *. apply Eval_eval in H7.
    rewrite H7. reflexivity.
  - intros. inversion H; subst.
    + simpl. reflexivity.
    + simpl. apply IHs1 in H7.
      rewrite H7. reflexivity.
  - intros. inversion H; subst.
    + apply Eval_eval in H8.
      simpl. rewrite H8.
      unfold not in H9.
      destruct (eq_nat_dec n 0).
      * apply H9 in e0. inversion e0.
      * reflexivity.
    + simpl in *. 
      apply Eval_eval in H8.
      rewrite H8. simpl. reflexivity.
 - intros. inversion H; subst.
    + simpl in *.
      apply Eval_eval in H4.
      rewrite H4.
      destruct (eq_nat_dec n 0).
      * unfold not in H8. apply H8 in e0. inversion e0.
      * reflexivity.
    + simpl in *.
      apply Eval_eval in H4.
      rewrite H4. simpl. reflexivity.
  - intros. inversion H; subst.
    simpl in *. reflexivity.
  - intros. inversion H; subst. 
    + simpl in *. reflexivity.
    + simpl in *. reflexivity.
Qed.

(* END PROBLEM 9 *)

(* StepN as seen in class *)
Inductive StepN : list Heap -> Heap -> Stmt -> nat ->
                  list Heap -> Heap -> Stmt -> Prop :=
| StepN_refl : forall l h s,
  StepN l h s 0 l h s
| StepN_step : forall l h s l' h' s' l'' h'' s'' n,
  Step l h s l' h' s' ->
  StepN l' h' s' n l'' h'' s'' ->
  StepN l h s (S n) l'' h'' s''.

(* [Problem 10 (5 points)] *)
(* Implement stepn as a function. *)
Fixpoint stepn (l: list Heap) (h: Heap) (s: Stmt) (n: nat) :
  option (list Heap * Heap * Stmt) :=
  match n with
  | 0 => Some (l, h, s)
  | S n' => 
      match step l h s with
      | None => None
      | Some (l', h', s') =>
          stepn l' h' s' n'
      end
  end.

(* END PROBLEM 10 *)

(* [Problem 11 (5 points)] *)
(* Prove your stepn function SOUND. *)
Lemma stepn_StepN:
  forall n l h s l' h' s',
  stepn l h s n = Some (l', h', s') ->
  StepN l h s n l' h' s'.
Proof.
  induction n.
  - intros. inversion H; subst.
    constructor.
  - intros. simpl in H.
    destruct (step l h s) as [[[myl myh] mys]|] eqn:?.
    + apply IHn in H.
      econstructor.
      * apply step_Step in Heqo. eapply Heqo.
      * apply H.
    + inversion H; subst.
Qed.
  (* About 14 tactics *)

(* END PROBLEM 11 *)

(* [Problem 12 (5 points)] *)
(* Prove your stepn function COMPLETE. *)
Lemma StepN_stepn:
  forall l h s n l' h' s',
  StepN l h s n l' h' s' ->
  stepn l h s n = Some (l', h', s').
Proof.
  intros l h s n. revert l h s.
  induction n.
  - intros.
    inversion H; subst.
    simpl. reflexivity.
  - intros.
    inversion H; subst.
    simpl in *.
    apply IHn in H5.
    apply Step_step in H1.
    rewrite H1. apply H5.
Qed.

(* END PROBLEM 12 *)

(* The run function, which takes up to n steps. *)
Fixpoint run (n: nat) (l: list Heap) (h: Heap) (s: Stmt) : list Heap * Heap * Stmt :=
  match n with
    | O => (l, h, s)
    | S m =>
      match step l h s with
        | Some (l', h', s') => run m l' h' s'
        | None => (l, h, s)
      end
  end.

(* [Problem 13 (5 points)] *)
(* Define the StepStar relation, which corresponds to taking any number of steps. *)
Inductive StepStar : list Heap -> Heap -> Stmt ->
                     list Heap -> Heap -> Stmt -> Prop :=
| step_star_0:
    forall l h s, StepStar l h s l h s
| step_star_more:
    forall l h s l1 h1 s1 l2 h2 s2,
      Step l h s l1 h1 s1
        -> StepStar l1 h1 s1 l2 h2 s2
            -> StepStar l h s l2 h2 s2.

(* END PROBLEM 13 *)


(* [Problem 14 (5 points)] *)
(* Prove that run is SOUND with respect to StepStar. *)
Lemma run_StepStar:
  forall n l h s l' h' s',
  run n l h s = (l', h', s') -> StepStar l h s l' h' s'.
Proof.
  induction n.
  - intros. simpl in *. inversion H; subst.
    constructor.
  - intros. simpl in *.
    destruct (step l h s) as [[[myl myh] mys]|] eqn:?.
    + apply step_Step in Heqo.
      apply IHn in H.
      econstructor.
      * eapply Heqo.
      * apply H.
    + inversion H; subst.
      constructor.
Qed.

(* END PROBLEM 14 *)

(* [Problem 15 (5 points)] *)
(* Prove that running a state that can't step gives that same state. *)
Lemma nostep_run_refl:
  forall l h s, step l h s = None ->
           forall n, run n l h s = (l, h, s).
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite H.
    reflexivity.
Qed.
(* END PROBLEM 15 *)

(* [Problem 16 (5 points)] *)
(* Prove that two consecutive runs are the same as one bigger run. *)
Lemma run_combine:
  forall m n l h s l' h' s' l'' h'' s'',
  run m l h s = (l', h', s') ->
  run n l' h' s' = (l'', h'', s'') ->
  run (m + n) l h s = (l'', h'', s'').
Proof.
  induction m.
  - intros. simpl. inversion H; subst. apply H0.
  - intros. simpl.
    destruct (step l h s) as [[[myl myh] mys]|] eqn:?.
    + eapply IHm.
      simpl in H. rewrite Heqo in H; simpl.
      eapply H. apply H0.
    + simpl in H. rewrite Heqo in H; simpl.
      inversion H; subst.
      apply step_None_Skip in Heqo. subst.
      destruct n.
      * simpl in *. apply H0.
      * simpl in H0. apply H0.
Qed.

(* END PROBLEM 16 *)

(* Here we define what it means for a statement to contain a while. *)
Fixpoint hasWhile (s: Stmt) : bool :=
  match s with
    | Skip => false
    | Assign _ _ => false
    | Seq s1 s2 => orb (hasWhile s1) (hasWhile s2)
    | Cond _ s1 s2 =>  orb (hasWhile s1) (hasWhile s2)
    | While _ _ => true
    | PushHeap => false
    | PopHeap _ => false
  end.

(* Here we define the number of PushHeap statements contained in a statement. *)
Fixpoint nPushHeap (s: Stmt) : nat :=
  match s with
    | Skip => 0
    | Assign _ _ => O
    | Seq s1 s2 => nPushHeap s1 + nPushHeap s2
    | Cond _ s1 s2 => nPushHeap s1 + nPushHeap s2
    | While _ s1 => nPushHeap s1
    | PushHeap => 1
    | PopHeap _ => 0
  end.

(*
  [Problem 17 (5 points)]
  Prove that if we take a step from a statement without any whiles,
  then the resulting statement still has no whiles.
*)
Lemma hasWhileStep:
  forall l h s l' h' s',
    Step l h s l' h' s' ->
    hasWhile s = false ->
    hasWhile s' = false.
Proof.
  intros l h s; revert l h.
  induction s.
  - intros. inversion H.
  - intros. inversion H; subst. simpl. reflexivity.
  - intros. inversion H; subst.
    + simpl in H0. apply H0.
    + simpl in H0. apply orb_false_elim in H0.
      inversion H0. simpl.
      rewrite H2. 
      apply IHs1 in H8.
      * rewrite H8. simpl. reflexivity.
      * apply H1.
  - intros. simpl in *.
    apply orb_false_elim in H0. inversion H0.
    inversion H; subst.
    + apply H1.
    + apply H2.
  - intros. simpl in H0. inversion H0.
  - intros. inversion H; subst. simpl; reflexivity.
  - intros. inversion H; subst.
    + simpl; reflexivity.
    + simpl; reflexivity.
Qed.
(* END PROBLEM 17 *)

(* *** A BIT TRICKY! *** *)
(*
  [Problem 18 (10 points)]

  State and prove the following property:
    If statement s has no While loops and from the empty stack
    (l = nil) and empty heap (h = nil), s can step to stack l',
    heap h', and statement s', then the length of l' does not
    exceed the number of PushHeap statements in s (the original
    statement).

  Hints:
    - You will need two lemmas to prove this.
    - Think carefully about your induction hypotheses.
*)


Lemma Heap_onestep:
forall s l h l' h' s',
  Step l h s l' h' s'
  -> hasWhile s = false -> le (length l' + nPushHeap s') ((length l) + nPushHeap s).
Proof.
  induction s.
  - intros. simpl in *. inversion H; subst.
  - intros. simpl in *. inversion H; subst. simpl. omega.
  - intros. simpl in *. inversion H; subst.
    + omega.
    + apply orb_false_elim in H0; inversion H0. simpl in *.
      assert (HH1: length l' + nPushHeap s1' <= length l + nPushHeap s1 
        -> length l' + (nPushHeap s1' + nPushHeap s2) <= length l + (nPushHeap s1 + nPushHeap s2)).
      * omega.
      * eapply HH1. eapply IHs1.
        apply H8. apply H1.
  - intros. simpl in *. inversion H; subst.
    + omega.
    + omega.
  - intros. inversion H0.
  - intros. simpl. inversion H; subst. simpl. omega.
  - intros. simpl. inversion H; subst. 
    + simpl. omega.
    + simpl. omega.
Qed.

Theorem Heap_n_step:
  forall n s l h l' h' s',
  StepN l h s n l' h' s'
  -> hasWhile s = false -> le (length l' + nPushHeap s') (nPushHeap s + length l).
Proof.
  induction n.
  - intros. inversion H. subst. simpl. omega.
  - intros. inversion H. subst. 
    assert (H_l'0_l': length l' +  nPushHeap s' <= nPushHeap s'0 + length l'0).
    + eapply IHn. eapply H6. eapply hasWhileStep.
      apply H2. apply H0.
    + apply Heap_onestep in H2. 
      assert (HH1: length l' + nPushHeap s' <= length l'0 + nPushHeap s'0
                  -> length l'0 + nPushHeap s'0 <= length l + nPushHeap s
                  -> length l' + nPushHeap s' <= nPushHeap s + length l).
      * omega.
      * apply HH1. omega. apply H2.
      * apply H0.
Qed.

Theorem Heap_fromEmpty_step:
  forall n s l' h' s',
  StepN [] [] s n l' h' s'
  -> hasWhile s = false -> le (length l') (nPushHeap s).
Proof.
  intros. specialize (Heap_n_step).
  intros. apply H1 in H.
  simpl in H.
  assert (H_Finally: length l' + nPushHeap s' <= nPushHeap s + 0 -> length l' <= nPushHeap s).
  - omega.
  - apply H_Finally.
    apply H.
  - apply H0.
Qed.

(*
  [Problem 19 (5 points)]

  Prove the previous claim is false if we allow s to contain
  While loops.

  Hint:
    - No need to use induction.
*)

Eval compute in run 5 [] [] (While (Int 1) (PushHeap)).



Theorem Heap_wrong: 
~(forall n s l' h' s', StepN [] [] s n l' h' s' 
    -> hasWhile s = true -> le (length l') (nPushHeap s)).
Proof.
  intro H.
  specialize (H 5 (While (Int 1) (PushHeap)) [[]; []] [] (Seq Skip (While (Int 1) PushHeap))).
  simpl in H.
  assert (H0: StepN [] [] (While (Int 1) PushHeap) 5 [[]; []] []
      (Seq Skip (While (Int 1) PushHeap))).
  + apply stepn_StepN; reflexivity.
  + intuition.
Qed.
