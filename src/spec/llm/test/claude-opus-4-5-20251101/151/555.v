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

Definition double_the_difference_real_spec (lst : list R) (result : Z) : Prop :=
  result = 0%Z.

Example test_real_list : double_the_difference_real_spec (1.25%R :: 2.5%R :: 3.5639643956938984%R :: (-5.5)%R :: nil) 0%Z.
Proof.
  unfold double_the_difference_real_spec.
  reflexivity.
Qed.