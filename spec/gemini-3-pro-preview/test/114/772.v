Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
      match l with
      | [] => global_min
      | y :: ys =>
        let new_current_min := Z.min y (current_min + y) in
        let new_global_min := Z.min global_min new_current_min in
        aux ys new_current_min new_global_min
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-10; -9; -8; -7; -6; -5; -4; -99; -3; -2; -1; -8] = -162.
Proof.
  compute.
  reflexivity.
Qed.