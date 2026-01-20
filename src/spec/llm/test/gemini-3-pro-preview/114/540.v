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
        let new_current := Z.min y (current_min + y) in
        let new_global := Z.min global_min new_current in
        aux ys new_current new_global
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [10; -20; 30; -40; 50; -60; 70; 11; -80; 60; 90; -100] = -100.
Proof.
  reflexivity.
Qed.