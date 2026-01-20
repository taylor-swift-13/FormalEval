Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let new_current_min := Z.min x (current_min + x) in
      let new_min_so_far := Z.min min_so_far new_current_min in
      min_sub_array_sum_aux xs new_current_min new_min_so_far
  end.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux xs x x
  end.

Example test_case: min_sub_array_sum [0%Z; -2%Z; 3%Z; -4%Z; 4%Z; 5%Z; -6%Z; 7%Z; 49%Z; 10%Z; 9%Z; -10%Z; -4%Z; -6%Z; 10%Z] = -20%Z.
Proof. compute. reflexivity. Qed.