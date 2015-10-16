(* Homework 01 (90 total points) *)

(*
  In this homework, you'll do some programming in Coq and do some simple proofs.

  Each problem should be independent of the others, but subproblems
   may depend on each other.

  Later problems aren't necessarily harder than earlier ones, so if you get
   stuck on a problem, move on and come back to it later.

  You'll know most of what you need for this homework after the first lecture,
   and everything by the second. Get started early so you have time to ask questions!

  For all proofs, please use bullets ( -, +, * ) as shown in class. For this homework,
   we won't take points off for proof style, but we may start doing so in future.

*)

(* Multiplication of natural numbers, used in problem 1 *)
Fixpoint mult m n :=
  match m with
    | 0 => 0
    | S m' => plus n (mult m' n)
  end.

(* [PROBLEM 1 (5 points)]: Prove that multiplication by 1 is the identity.
   Hint: this should be similar to add_O from Lecture 1 *)

Lemma mult_1 :
  forall m,
    mult m 1 = m.
Proof.
  (* about 7 tactics *)
  intros m.
  induction m.
  - simpl. reflexivity.
  - simpl.
    rewrite IHm.
    reflexivity.
Qed.
(* Change "Admitted" to "Qed" when the proof is completed. *)
(* END PROBLEM 1 *)

(* Decide if two nats are equal *)
Fixpoint nat_eq (m n: nat) : bool :=
  match m, n with
    | O, O => true
    | S mp, S np => nat_eq mp np
    | _, _ => false
  end.


(* [PROBLEM 2 (10 points)]:
    a (5 points). Correct the definition of nat_le, which returns
      true when m is less than or equal to n and false otherwise.
      Hint: this definition should be similar to nat_eq
    b (5 points). Complete the proof of nat_eq_nat_le, which states
      that if m = n, then m <= n.
      Hint: as is often the case, you may want to induct before intro-ing.
*)


Fixpoint nat_le (m n : nat) : bool := 
  (* fix this definition *)
  match m, n with
    | O, _ => true
    | S mp, S np => nat_le mp np
    | _, _ => false
  end.

(* Use these to test your function *)
Eval cbv in (nat_le 5 5). (* true *)
Eval cbv in (nat_le 3 5). (* true *)
Eval cbv in (nat_le 5 3). (* false *)

Theorem nat_eq_nat_le :
  forall m n,
    nat_eq m n = true ->
    nat_le m n = true.
Proof.
  (* about 10 tactics *)
  induction m.
  intros.
  - simpl. reflexivity.
  - intros.
    rewrite <- H.
    simpl.
    destruct n.
    + reflexivity.
    + simpl in H.
      rewrite IHm.
      * rewrite H. reflexivity.
      * rewrite H. reflexivity.
Qed.

Theorem nat_eq_nat_le_secondtry :
  forall m n,
    nat_eq m n = true ->
    nat_le m n = true.
Proof.
  induction m.
  - intros. simpl. reflexivity.
  - intros. simpl.
    destruct n.
    + inversion H.
    + simpl in H.
      apply IHm.
      apply H.
Qed.

(* END PROBLEM 2 *)

(* The following definitions are used in Problems 3-4 *)

(* "Counting" numbers *)

Inductive counting : Set :=
| one : counting
| next : counting -> counting.

(* integers *)
Inductive int : Set :=
| zero : int
| pos : counting -> int
| neg : counting -> int.

(* [PROBLEM 3 (8 points)]: Here are two other possible definitions of the integers:

Inductive int1 :=
| O : int1
| pred : int1 -> int1
| succ : int1 -> int1.

Inductive int2 :=
| pos : nat -> int2
| neg : nat -> int2.

Fixpoint pos_int (int : int1, intb : int 1) :=
  match int with
  | O -> false
  | pred n1, succ n2 -> 

pred (succ (pred (succ O)))

What is a potenial problem with these definitions? Explain briefly in a comment. 

My opinion: 1) Given an integer, we cannot get its sign from it without using another type. (first one)
            2) Comparing the equivalence/greater/less relations of two integer is not possible  (first one)
            3) pos O and neg O, equivlence is not defined. (second one)
*)

(* END PROBLEM 3 *)

(* Predecessor of an integer. Used in Problem 4. *)
Definition pred (x : int) : int :=
  match x with
    | zero => neg one
    | pos n => match n with
                | one => zero
                | next n' => pos n'
              end
    | neg n => neg (next n)
  end.

(* [Problem 4 (12 points)]:
   a (6 points). Correct the definition of succ, below.
      succ should return the successor of its argument,
       i.e., the next larger integer.
   b (6 points). Complete the proofs of pred_succ and succ_pred.
      Hint: induction is not necessary.
 *)

Definition succ (x : int) : int := 
  match x with
    | zero => pos one
    | pos n => pos (next n)
    | neg n => 
        match n with
          | one => zero
          | next n2 => neg n2
        end
    end.

Lemma pred_succ :
  forall x, pred (succ x) = x.
Proof.
  (* about 12 tactics *)
  intros x.
  destruct x.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma succ_pred :
  forall x, succ (pred x) = x.
Proof.
  (* about 12 tactics *)
  intros x.
  destruct x.
  - simpl. reflexivity.
  - simpl.
    destruct c.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity.
Qed.
(* END PROBLEM 4 *)

(* Binary trees of nats. Used in the remaining problems. *)
Inductive nat_tree : Set :=
| Leaf : nat_tree
| Branch : nat -> nat_tree -> nat_tree -> nat_tree.

(* size returns the number of nats in a tree. *)
Fixpoint size (nt: nat_tree) : nat :=
  match nt with
    | Leaf => 0
    | Branch n ntl ntr => S (plus (size ntl) (size ntr))
  end.

(* [PROBLEM 5 (5 points)]: Define sum to add up all the nats in a nat_tree. *)

Fixpoint sum (nt: nat_tree) : nat := 
  match nt with 
  | Leaf => 0
  | Branch n ntl ntr => plus n (plus (sum ntl) (sum ntr)) 
  end.

(* END PROBLEM 5 *)

(* [PROBLEM 6 (5 points)]: Define prod to multiply all the nats in a nat_tree.
     Hint: prod should call mult, defined above. *)

Fixpoint prod (nt: nat_tree) : nat := 
  match nt with
  | Leaf => 0
  | Branch n ntl ntr => mult n (mult (prod ntl) (prod ntr))
  end.

(* END PROBLEM 6 *)

(* fold over nat_trees *)
Fixpoint fold {T: Type} (base: T) (f: T -> nat -> T) (nt: nat_tree) : T :=
  match nt with
    | Leaf => base
    | Branch n l r => f (fold (fold base f l) f r) n
  end.

(* [PROBLEM 7 (3 points)]: Define sum' to add up all the nats in a nat_tree.
For full credit, do not use recursion (keep the Definition, don't change to Fixpoint).
*)

Check (fold 0).

Definition sum' (nt: nat_tree):= 
  fold 0 plus nt.

(* END PROBLEM 7 *)

(* [PROBLEM 8 (3 points)]: Define prod' to multiply up all the nats in a nat_tree.
For full credit, do not use recursion (keep the Definition, don't change to Fixpoint).
 *)

Definition prod' (nt: nat_tree):= fold 1 mult nt.

(* END PROBLEM 8 *)

(* [PROBLEM 9 (5 points)]: Define increment_all to add one to all the nats in a nat_tree.
*)

Fixpoint increment_all (nt: nat_tree) : nat_tree :=
  match nt with
  | Leaf => Leaf
  | Branch n l r => Branch (plus 1 n) (increment_all l) (increment_all r)
  end.

(* END PROBLEM 9 *)

(* [PROBLEM 10 (5 points)]: Define double to multiply all the nats in a nat_tree by 2.
*)

Fixpoint double (nt: nat_tree) : nat_tree :=
  match nt with
  | Leaf => Leaf
  | Branch n l r => Branch (mult n 2) (double l) (double r)
  end.

(* END PROBLEM 10 *)

(* [PROBLEM 11 (12 points)]:
   a (6 points). Define map to apply a function of type nat -> nat
     to every nat in a nat_tree.
     The resulting tree should have exactly the same structure as the initial tree.
   b (6 points). Complete the proof of size_map, which proves that map preserves the
     size of a tree.
 *)

Fixpoint map (f: nat -> nat) (nt: nat_tree) : nat_tree :=
   match nt with
    | Leaf => Leaf
    | Branch n l r => Branch (f n) (map f l) (map f r)
   end.

Theorem size_map : forall f t, size (map f t) = size t.
Proof.
  (* about 7 tactics *)
  induction t.
  - simpl. reflexivity.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

(* END PROBLEM 11 *)

(* [PROBLEM 12 (12 points)]:
   a (6 points). Define mirror to flip all the branches in the tree:
               5              5
              / \            / \
             3   4     =>   4   3
            / \                / \
           1   6              6   1
      (leaves are not displayed above)
   b (6 points). Complete the proof of size_mirror, which proves that mirror preserves the
     size of a tree.
*)

Fixpoint mirror (nt: nat_tree) : nat_tree :=
  (* fill in your definition of mirror here *)
  match nt with
    | Leaf => Leaf
    | Branch n l r => Branch n (mirror l) (mirror r)
   end.

Theorem size_mirror : forall t, size (mirror t) = size t.
Proof.
  (* about 8 tactics *)
  induction t.
  - simpl. reflexivity.
  - simpl. 
    rewrite IHt1.
    rewrite IHt2.
    reflexivity. 
Qed.

(* END PROBLEM 12 *)

(* [PROBLEM 13 (10 points)]:
Consider this alternate definition of fold:
*)
Fixpoint fold' {T: Type} (base: T) (f: T -> nat -> T) (nt: nat_tree) : T :=
  match nt with
    | Leaf => base
    | Branch n l r => fold' (f (fold' base f l) n) f r
  end.
(*
In a short English paragraph, describe how fold and fold' differ.
*)

(* WRITE HERE *)

(*Answer: The difference between these two functions is that the fold function would firstly
compute the value of the left tree, then compute the value of the right tree based
on the result of left tree, then finally add the value of the current node to the 
computation result after finished computing the right sub tree. However, the fold'
function would 1) visit the left tree, 2) compute the value of the current node to
the result and then 3) compute the value of the right tree based on the result.

In another word, fold visits the tree in post-order (after the the visit of both 
left and right sub tree) while fold' visits the tree in in-order (visit the left 
sub-tree, then the current node, and finally the rightsub-tree). *)

(* END PROBLEM 13 *)

(*
OPTIONAL Bonus:

What should be true about a particular f for the following to hold:

  forall b nt, fold b f nt = fold' b f nt

  (* TODO write here *)
  The condition is that: forall x:T y:nat z:nat f (f x y) z = f (f x z) y.

Optional Bonus 2: Formalize this property in Coq, and prove that
  forall f b nt, <property> f -> fold b f nt = fold' b f nt.
*)

(* Lemma f_fold': forall f nt, (forall y z (x:bool), f (f x y) z = f (f x z) y) 
  -> forall  u v, f (fold' u f nt) v = fold' (f u v) f nt.
Proof.
  induction nt.
  - simpl. reflexivity.
  - simpl.
    intros.
    rewrite <- IHnt1.
    rewrite H.
    rewrite -> IHnt2.
    reflexivity.
    * apply H.
    * apply H.
Qed.
*)
Lemma f_fold: forall f nt, (forall y z (x:bool),
  f (f x y) z = f (f x z) y) ->
      forall  u v, f (fold u f nt) v = fold (f u v) f nt.
Proof.
  induction nt.
  - simpl. reflexivity.
  - simpl.
    intros.
    rewrite <- IHnt1.
    rewrite H.
    rewrite -> IHnt2.
    reflexivity.
    * apply H.
    * apply H.
Qed.

Lemma zach: forall f nt b, (forall y z (x:bool), f (f x y) z = f (f x z) y) 
  -> fold b f nt = fold' b f nt.
Proof.
  induction nt.
  - simpl. reflexivity.
  - simpl.
    intros.
    rewrite <- IHnt1.
    + destruct nt1.
      *  simpl. rewrite f_fold.
         intros. rewrite <- IHnt2.
          reflexivity. apply H. apply H.
      * simpl. rewrite f_fold.
        rewrite <- IHnt2.
        reflexivity. apply H. apply H.
    + apply H.
Qed.
  