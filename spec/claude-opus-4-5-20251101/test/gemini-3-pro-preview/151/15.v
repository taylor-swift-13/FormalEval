Require Import ZArith.
Require Import List.
Require Import Reals.
Open Scope Z_scope.

Inductive Number :=
| NumInt (z : Z)
| NumReal (r : R).

Definition is_positive_odd_integer (n : Z) : bool :=
  (n >? 0) && (n mod 2 =? 1).

Fixpoint sum_of_squares_of_positive_odd_integers (lst : list Number) : Z :=
  match lst with
  | nil => 0
  | x :: xs => 
      match x with
      | NumInt n => if is_positive_odd_integer n 
                    then n * n + sum_of_squares_of_positive_odd_integers xs
                    else sum_of_squares_of_positive_odd_integers xs
      | NumReal _ => sum_of_squares_of_positive_odd_integers xs
      end
  end.

Definition double_the_difference_spec (lst : list Number) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers lst.

Example test_case_1 : double_the_difference_spec 
  (NumInt 2 :: NumReal (5/2)%R :: NumInt 3 :: NumReal (7/2)%R :: NumInt 4 :: NumReal (9/2)%R :: NumInt 5 :: nil) 
  34.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.