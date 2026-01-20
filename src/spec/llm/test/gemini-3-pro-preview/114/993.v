Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min global_min new_current in
      min_sub_array_sum_aux xs new_current new_global
  end.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux xs x x
  end.

Example test_min_sub_array_sum: min_sub_array_sum [1; -4; 6; -6; 7; -8; 9; 4; -2; 2] = -8.
Proof. reflexivity. Qed.