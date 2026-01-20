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
  min_sub_array_sum [50; -50; 100; -100; 50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -50; 99; 50] = -100.
Proof.
  reflexivity.
Qed.