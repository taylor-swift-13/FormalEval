Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr_min : Z) (global_min : Z) : Z :=
      match l with
      | [] => global_min
      | y :: ys =>
        let new_curr := Z.min y (curr_min + y) in
        let new_global := Z.min global_min new_curr in
        aux ys new_curr new_global
      end
    in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -90%Z; -6%Z; 2%Z; 9%Z; 4%Z; 1%Z; 6%Z; 2%Z; -7%Z; -1%Z; -6%Z] = -96%Z.
Proof. reflexivity. Qed.