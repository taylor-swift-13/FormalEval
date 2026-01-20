Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
        let new_current := Z.min y (current_min + y) in
        let new_global := Z.min global_min new_current in
        aux ys new_current new_global
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [-10%Z; -9%Z; -8%Z; -1%Z; -7%Z; -6%Z; -5%Z; 49%Z; -3%Z; 50000%Z; -2%Z; 100000%Z; -1%Z; -9%Z] = -46%Z.
Proof. reflexivity. Qed.