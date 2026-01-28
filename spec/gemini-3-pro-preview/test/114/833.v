Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(final_min, _) :=
        fold_left (fun acc y =>
          let '(min_so_far, current_min) := acc in
          let new_current_min := Z.min y (current_min + y) in
          (Z.min min_so_far new_current_min, new_current_min)
        ) xs (x, x)
      in final_min
  end.

Example test_minSubArraySum: minSubArraySum [1; 3; -4; 5; -6; 7; -6; -8; 9; 4; -2; 2; 5] = -14.
Proof.
  compute. reflexivity.
Qed.