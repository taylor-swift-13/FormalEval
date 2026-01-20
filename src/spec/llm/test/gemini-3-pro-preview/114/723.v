Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | y :: ys =>
        let new_current := Z.min y (current + y) in
        let new_min_so_far := Z.min min_so_far new_current in
        aux ys new_current new_min_so_far
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum: min_sub_array_sum [-2; -3; -4; 50000; 5; -6; 7; -8; -3; 2; -1; 4; -8] = -14.
Proof. reflexivity. Qed.