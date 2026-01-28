Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint min_sub_array_sum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
    let current_min' := Z.min x (current_min + x) in
    let min_so_far' := Z.min min_so_far current_min' in
    min_sub_array_sum_aux xs current_min' min_so_far'
  end.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_array_sum_aux xs x x
  end.

Example test_min_sub_array_sum: min_sub_array_sum [-80%Z; 1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -50000%Z; -8%Z; 9%Z; 10%Z; 4%Z; 1%Z; 2%Z; 70%Z; -99999%Z; 7%Z] = -149987%Z.
Proof. reflexivity. Qed.