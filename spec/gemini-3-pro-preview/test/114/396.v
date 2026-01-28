Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
        match l with
        | [] => global_min
        | y :: ys =>
            let next_min := Z.min y (current_min + y) in
            aux ys next_min (Z.min global_min next_min)
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1; -2; 3; -9; -4; -1; 5; -6; 7; -8; 9; -10; -10; -10] = -37.
Proof. reflexivity. Qed.