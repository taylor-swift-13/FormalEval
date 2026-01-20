Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
        match l with
        | [] => global_min
        | y :: ys =>
            let current_min' := Z.min y (current_min + y) in
            let global_min' := Z.min global_min current_min' in
            aux ys current_min' global_min'
        end
      in aux xs x x
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -100%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -101%Z.
Proof. reflexivity. Qed.