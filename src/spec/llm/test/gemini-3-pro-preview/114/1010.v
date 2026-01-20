Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_subarray_sum_aux (l : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match l with
  | [] => min_so_far
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min min_so_far new_current in
      min_subarray_sum_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_subarray_sum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 50000%Z; 100000%Z; -50000%Z; -10%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z; -50000%Z; 50000%Z; -100000%Z; 100000%Z] = -150010%Z.
Proof. reflexivity. Qed.