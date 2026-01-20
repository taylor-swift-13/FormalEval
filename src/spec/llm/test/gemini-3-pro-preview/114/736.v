Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
  match l with
  | [] => global_min
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min global_min new_current in
      min_sub_array_sum_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [-10; -9; -7; -6; -5; -3; -9; -100; -1; -1; -5] = -156.
Proof.
  reflexivity.
Qed.