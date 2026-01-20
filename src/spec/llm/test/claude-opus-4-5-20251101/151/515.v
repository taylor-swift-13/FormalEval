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

Example test_mixed_list : double_the_difference_spec ((-5)%Z :: 7%Z :: (-11)%Z :: (-14)%Z :: (-16)%Z :: 19%Z :: 24%Z :: 25%Z :: 6%Z :: (-28)%Z :: 5%Z :: nil) 1060%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.