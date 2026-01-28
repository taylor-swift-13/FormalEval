Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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
            let next_current := Z.min y (current_min + y) in
            let next_global := Z.min global_min next_current in
            aux ys next_current next_global
        end
      in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [-8%Z; -9%Z; 20%Z; -30%Z; 40%Z; -50%Z; 60%Z; -70%Z; 80%Z; -90%Z; 100%Z] = -90%Z.
Proof.
  reflexivity.
Qed.