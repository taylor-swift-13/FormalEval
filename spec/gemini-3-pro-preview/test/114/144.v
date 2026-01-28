Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_sum : Z) (min_sum : Z) : Z :=
      match l with
      | [] => min_sum
      | y :: ys =>
        let new_current := Z.min y (current_sum + y) in
        let new_min := Z.min min_sum new_current in
        aux ys new_current new_min
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1; -1; 1; -1; -1; 1; -1; 1; -9; -1; 1; -1] = -11.
Proof. reflexivity. Qed.