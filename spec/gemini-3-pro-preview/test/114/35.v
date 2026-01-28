Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_subarray_sum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let current_min' := Z.min x (current_min + x) in
      let min_so_far' := Z.min min_so_far current_min' in
      min_subarray_sum_aux xs current_min' min_so_far'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_subarray_sum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-2%Z; 1%Z; 2%Z; 6%Z; -7%Z; -3%Z; -5%Z; 1%Z; -2%Z] = -16%Z.
Proof. reflexivity. Qed.