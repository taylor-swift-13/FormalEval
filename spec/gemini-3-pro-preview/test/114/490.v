Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_min : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | y :: ys =>
        let new_curr := Z.min y (current_min + y) in
        aux ys new_curr (Z.min min_so_far new_curr)
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1; -2; 3; -4; 5; -6; 7; -8; 9; 4; 1; 6; 1; -7; -6] = -13.
Proof. reflexivity. Qed.