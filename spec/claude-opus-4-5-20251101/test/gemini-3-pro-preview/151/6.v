Require Import ZArith.
Require Import List.
Require Import Reals.
Open Scope Z_scope.

Inductive Number : Type :=
| NumZ (z : Z)
| NumR (r : R).

Definition is_positive_odd_integer (n : Z) : bool :=
  (n >? 0) && (n mod 2 =? 1).

Fixpoint sum_of_squares_of_positive_odd_integers (lst : list Number) : Z :=
  match lst with
  | nil => 0
  | x :: xs => match x with
               | NumZ z => if is_positive_odd_integer z 
                           then z * z + sum_of_squares_of_positive_odd_integers xs
                           else sum_of_squares_of_positive_odd_integers xs
               | NumR _ => sum_of_squares_of_positive_odd_integers xs
               end
  end.

Definition double_the_difference_spec (lst : list Number) (result : Z) : Prop :=
  result = sum_of_squares_of_positive_odd_integers lst.

Example test_case_1 : double_the_difference_spec (NumR (IZR 2 / IZR 10)%R :: NumZ 3 :: NumZ 5 :: nil) 34%Z.
Proof.
  unfold double_the_difference_spec.
  simpl.
  reflexivity.
Qed.