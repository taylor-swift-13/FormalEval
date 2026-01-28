Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr_min : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | y :: ys =>
        let new_curr := Z.min y (curr_min + y) in
        let new_so_far := Z.min min_so_far new_curr in
        aux ys new_curr new_so_far
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -29%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z] = -33%Z.
Proof. reflexivity. Qed.