Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

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

Example test_min_sub_array_sum: min_sub_array_sum [-3%Z; -5%Z; -8%Z; -3%Z; -2%Z; -4%Z; -10%Z] = -35%Z.
Proof. reflexivity. Qed.