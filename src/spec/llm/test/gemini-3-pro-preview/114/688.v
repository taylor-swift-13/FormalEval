From Coq Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_min global_min : Z) : Z :=
      match l with
      | [] => global_min
      | y :: ys =>
        let current_min' := Z.min y (current_min + y) in
        let global_min' := Z.min global_min current_min' in
        aux ys current_min' global_min'
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-10; -9; -8; -7; -6; -5; -100000; -4; -3; -2; -2; -9] = -100065.
Proof. reflexivity. Qed.