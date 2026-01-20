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

Definition extract_integers_from_mixed_list : list Z :=
  (-5) :: (-29) :: 7 :: (-11) :: (-14) :: (-28) :: (-16) :: 19 :: 24 :: 26 :: (-28) :: (-29) :: nil.

Example test_mixed_list : double_the_difference_spec extract_integers_from_mixed_list 410%Z.
Proof.
  unfold double_the_difference_spec.
  unfold extract_integers_from_mixed_list.
  simpl.
  reflexivity.
Qed.