Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr_min : Z) (glob_min : Z) : Z :=
      match l with
      | [] => glob_min
      | y :: ys =>
        let new_curr := Z.min y (curr_min + y) in
        let new_glob := Z.min glob_min new_curr in
        aux ys new_curr new_glob
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [8; -2; 3; -4; 5; -6; 7; -90; -6; 9; 4; 1; 6; 2; -1; -6] = -96.
Proof. reflexivity. Qed.