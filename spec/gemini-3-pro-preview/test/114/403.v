Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
        let next_current := Z.min y (current_min + y) in
        let next_global := Z.min global_min next_current in
        aux ys next_current next_global
      end
    in aux xs x x
  end.

Example minSubArraySum_example : minSubArraySum [-8; -1; 2; -3; 4; 6; -7; 8; -9] = -10.
Proof. reflexivity. Qed.