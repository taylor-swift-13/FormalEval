Require Import ZArith.
Require Import List.
Require Import Reals.
Open Scope Z_scope.

Definition is_positive_odd_integer (n : Z) : bool :=
  (n >? 0) && (n mod 2 =? 1).

Fixpoint sum_of_squares_of_positive_odd_integers (lst : list (sum Z R)) : Z :=
  match lst with
  | nil => 0
  | inl x :: xs => if is_positive_odd_integer x 
               then x * x + sum_of_squares_of_positive_odd_integers xs
               else sum_of_squares_of_positive_odd_integers xs
  | inr _ :: xs => sum_of_squares_of_positive_odd_integers xs
  end.

Definition double_the_difference_spec (lst : list (sum Z R)) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers lst.

Example test_case_1 : double_the_difference_spec 
  ((inr 3.239486827292248%R) :: (inl 2) :: (inl (-5)) :: (inr 2.5%R) :: (inl 5) :: (inr 3.5%R) :: (inr 4.5%R) :: (inr 3.5%R) :: nil) 
  25.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.