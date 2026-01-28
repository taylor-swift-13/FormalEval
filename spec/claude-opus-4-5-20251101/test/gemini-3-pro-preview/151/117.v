Require Import ZArith.
Require Import List.
Require Import Reals.
Open Scope Z_scope.

Definition is_positive_odd_integer (n : Z) : bool :=
  (n >? 0) && (n mod 2 =? 1).

Fixpoint sum_of_squares_of_positive_odd_integers (lst : list Z) : Z :=
  match lst with
  | nil => 0
  | x :: xs => if is_positive_odd_integer x 
               then x * x + sum_of_squares_of_positive_odd_integers xs
               else sum_of_squares_of_positive_odd_integers xs
  end.

Definition double_the_difference_spec (lst : list Z) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers lst.

Example test_case_1 : double_the_difference_spec (12 :: 10 :: 1 :: 3 :: 5 :: 7 :: 9 :: 11 :: 13 :: 15 :: 17 :: 19 :: nil) 1330.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.