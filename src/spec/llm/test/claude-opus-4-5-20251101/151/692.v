Require Import ZArith.
Require Import List.
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

Example test_mixed_list : double_the_difference_spec 
  ((-2) :: (-4) :: (-5) :: 7 :: (-11) :: (-14) :: (-16) :: (-15) :: (-18) :: 19 :: 24 :: 25 :: 26 :: (-28) :: (-29) :: 26 :: nil) 
  1035%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.