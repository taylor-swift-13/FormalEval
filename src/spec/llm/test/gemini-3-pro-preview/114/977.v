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

Example test_minSubArraySum: minSubArraySum [89%Z; -10%Z; -9%Z; -7%Z; -6%Z; -3%Z; -70%Z; -2%Z; 49%Z; -5%Z; -7%Z] = -107%Z.
Proof. reflexivity. Qed.