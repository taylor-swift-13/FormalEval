Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr_min glob_min : Z) : Z :=
      match l with
      | [] => glob_min
      | y :: ys =>
        let curr_min' := Z.min y (curr_min + y) in
        let glob_min' := Z.min glob_min curr_min' in
        aux ys curr_min' glob_min'
      end
    in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [1; -70; -1; 1; 1; 0; -1; 1; -1; 0; -1; 2; -1] = -71.
Proof.
  reflexivity.
Qed.