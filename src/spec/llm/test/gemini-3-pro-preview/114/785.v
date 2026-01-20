Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (rest : list Z) (current_min : Z) (global_min : Z) : Z :=
        match rest with
        | [] => global_min
        | y :: ys =>
            let next_min := Z.min y (current_min + y) in
            aux ys next_min (Z.min global_min next_min)
        end
      in aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 90%Z; 0%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; -70%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 0%Z; 1%Z; 1%Z; -1%Z] = -72%Z.
Proof.
  compute. reflexivity.
Qed.