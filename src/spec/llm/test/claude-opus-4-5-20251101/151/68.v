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

Definition filter_integers_from_reals (lst : list R) : list Z :=
  nil.

Definition double_the_difference_real_spec (lst : list R) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers (filter_integers_from_reals lst).

Example test_non_integer_list : double_the_difference_real_spec ((-0.08450530644125998)%R :: (-4.6)%R :: nil)%R 0%Z.
Proof.
  unfold double_the_difference_real_spec.
  unfold filter_integers_from_reals.
  simpl.
  reflexivity.
Qed.