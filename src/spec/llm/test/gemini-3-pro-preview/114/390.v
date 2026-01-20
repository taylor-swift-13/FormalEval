Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (min_s : Z) : Z :=
      match l with
      | [] => min_s
      | y :: ys =>
        let new_curr := Z.min y (curr + y) in
        let new_min := Z.min min_s new_curr in
        aux ys new_curr new_min
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1; -2; 3; -4; 5; -6; 7; -90; -7; -6; 9; 4; 1; 6; 2; -7; -1; -6; -6] = -103.
Proof. reflexivity. Qed.