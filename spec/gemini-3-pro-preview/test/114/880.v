Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
    let new_current_min := Z.min x (current_min + x) in
    let new_global_min := Z.min global_min new_current_min in
    min_sub_array_sum_aux xs new_current_min new_global_min
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux xs x x
  end.

Example test_case_1: minSubArraySum [-70%Z; -1%Z; 1%Z; 0%Z; -1%Z; -8%Z; 1%Z; -1%Z; 1%Z; -1%Z; 2%Z; -1%Z] = -79%Z.
Proof. reflexivity. Qed.