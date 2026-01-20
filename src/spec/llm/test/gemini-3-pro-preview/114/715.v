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
        let next_min := Z.min y (current_min + y) in
        aux ys next_min (Z.min global_min next_min)
      end
    in aux xs x x
  end.

Example check: minSubArraySum [1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -1%Z.
Proof. reflexivity. Qed.