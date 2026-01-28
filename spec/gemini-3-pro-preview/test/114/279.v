Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

Example test_min_sub_array_sum: min_sub_array_sum [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -7%Z; 7%Z; -8%Z; 9%Z; -3%Z; 2%Z; -1%Z; -4%Z] = -8%Z.
Proof. reflexivity. Qed.