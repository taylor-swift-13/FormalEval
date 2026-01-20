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
            let new_current_min := Z.min y (current_min + y) in
            let new_global_min := Z.min global_min new_current_min in
            aux ys new_current_min new_global_min
        end
      in aux xs x x
  end.

Example test_minSubArraySum_1:
  minSubArraySum [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 18%Z; 8%Z; 9%Z; 10%Z; 10%Z; 10%Z; 10%Z; 19%Z; 10%Z; 11%Z; 12%Z; 13%Z; 15%Z; 1%Z] = 1%Z.
Proof.
  compute. reflexivity.
Qed.