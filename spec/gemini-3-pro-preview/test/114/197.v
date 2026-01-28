Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr_min : Z) (glob_min : Z) : Z :=
        match l with
        | [] => glob_min
        | y :: ys =>
            let new_curr := Z.min y (curr_min + y) in
            let new_glob := Z.min glob_min new_curr in
            aux ys new_curr new_glob
        end
      in aux xs x x
  end.

Example test_min_sub_array_sum : min_sub_array_sum [1; -2; 3; -4; 5; -6; 7; -8; 9; -10; -10; -8] = -28.
Proof.
  vm_compute.
  reflexivity.
Qed.