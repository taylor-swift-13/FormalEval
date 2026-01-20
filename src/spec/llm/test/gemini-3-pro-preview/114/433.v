Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (glob : Z) : Z :=
      match l with
      | [] => glob
      | y :: ys =>
        let new_curr := Z.min y (curr + y) in
        let new_glob := Z.min glob new_curr in
        aux ys new_curr new_glob
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [1; -2; 3; -30; 5; -6; -8; 9; 4; 4; 1; 6; 2; -1; -6] = -39.
Proof.
  reflexivity.
Qed.