Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (current_min : Z) (overall_min : Z) : Z :=
      match l with
      | [] => overall_min
      | y :: ys =>
        let current_min' := Z.min y (current_min + y) in
        let overall_min' := Z.min overall_min current_min' in
        aux ys current_min' overall_min'
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [-15; 2; -3; -4; 7; 8; -10] = -20.
Proof.
  reflexivity.
Qed.