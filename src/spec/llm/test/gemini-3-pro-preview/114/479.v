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

Example minSubArraySum_example :
  minSubArraySum [-1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 30%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; -1%Z] = -2%Z.
Proof.
  compute. reflexivity.
Qed.