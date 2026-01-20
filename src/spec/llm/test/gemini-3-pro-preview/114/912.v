Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr : Z) (min_so_far : Z) : Z :=
        match l with
        | [] => min_so_far
        | y :: ys =>
            let new_curr := Z.min y (curr + y) in
            let new_min := Z.min min_so_far new_curr in
            aux ys new_curr new_min
        end
      in aux xs x x
  end.

Example test_minSubArraySum_2:
  minSubArraySum [-10; -9; -8; -6; -5; -4; -3; -2; -1; -10; -8; -10] = -76.
Proof.
  reflexivity.
Qed.