Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
  match l with
  | [] => global_min
  | x :: xs =>
      let next_current := Z.min x (current_min + x) in
      let next_global := Z.min global_min next_current in
      min_sub_array_sum_aux xs next_current next_global
  end.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux xs x x
  end.

Example test_min_sub_array_sum: min_sub_array_sum [100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 49999%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 100%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; -100000%Z; -100000%Z] = -300000%Z.
Proof. reflexivity. Qed.