Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

Example test_minSubArraySum : minSubArraySum [10%Z; -20%Z; -40%Z; 50%Z; -60%Z; 70%Z; -80%Z; 60%Z; 90%Z; -100%Z; -40%Z] = -140%Z.
Proof. reflexivity. Qed.