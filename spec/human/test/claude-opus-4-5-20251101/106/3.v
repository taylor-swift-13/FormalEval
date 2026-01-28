(* Implement the function f that takes n as a parameter,
and returns a list of size n, such that the value of the element at index i is the factorial of i if i is even
or the sum of numbers from 1 to i otherwise.
i starts from 1.
the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
Example:
f(5) == [1, 2, 6, 24, 15] *)

Require Import Nat.
Require Import List.
Require Import Factorial.
Require Import Lia.
Import ListNotations.

Definition problem_106_pre (n : nat) : Prop := True.

Definition problem_106_spec (n : nat) (l : list nat) : Prop :=
  let sum := fun i => Nat.div (i * (i + 1)) 2 in
  length l = n /\
  (forall i, 1 <= i -> i <= n -> nth_error l (i - 1) = Some (if even i then fact i else sum i)).

Example problem_106_test : problem_106_spec 1 [1].
Proof.
  unfold problem_106_spec.
  split.
  - simpl. reflexivity.
  - intros i H1 H2.
    destruct i as [|i']; [lia|].
    destruct i' as [|i''].
    + (* i = 1 *)
      simpl. reflexivity.
    + (* i >= 2, contradiction with i <= 1 *)
      lia.
Qed.