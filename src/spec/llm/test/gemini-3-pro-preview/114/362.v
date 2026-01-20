Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (current_min : Z) (min_so_far : Z) (l : list Z) : Z :=
  match l with
  | [] => min_so_far
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_total := Z.min min_so_far new_current in
      min_sub_array_sum_aux new_current new_total xs
  end.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux x x xs
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [1%Z; -2%Z; 3%Z; -4%Z; -6%Z; 7%Z; -50000%Z; -8%Z; 9%Z; 10%Z; 4%Z; 1%Z; 2%Z; 70%Z; -1%Z; 7%Z] = -50011%Z.
Proof. reflexivity. Qed.