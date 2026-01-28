Require Import ZArith.
Require Import List.
Require Import Reals.
Open Scope Z_scope.

Definition is_positive_odd_integer (n : Z) : bool :=
  (n >? 0) && (n mod 2 =? 1).

Fixpoint sum_of_squares_of_positive_odd_integers (lst : list R) : Z :=
  match lst with
  | nil => 0
  | x :: xs => sum_of_squares_of_positive_odd_integers xs
  end.

Definition double_the_difference_spec (lst : list R) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers lst.

Example test_case_1 : double_the_difference_spec (cons (-0.08450530644125998)%R (cons (-4.6)%R nil)) 0%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.