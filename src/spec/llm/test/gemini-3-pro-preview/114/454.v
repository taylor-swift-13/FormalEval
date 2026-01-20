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

Example test_minSubArraySum: minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; -1%Z; -2%Z; 1%Z; -1%Z; 1%Z; -9%Z; -1%Z; 1%Z; -1%Z; -2%Z] = -15%Z.
Proof.
  compute. reflexivity.
Qed.