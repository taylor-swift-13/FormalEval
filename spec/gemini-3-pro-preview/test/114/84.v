Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_min : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | y :: ys =>
        let new_current_min := Z.min y (current_min + y) in
        let new_min_so_far := Z.min min_so_far new_current_min in
        aux ys new_current_min new_min_so_far
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-2%Z; -5%Z; -8%Z; -3%Z; -1%Z; -2%Z; -4%Z; -4%Z] = -29%Z.
Proof. reflexivity. Qed.