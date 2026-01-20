Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_subarray_sum_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
      let current_min' := Z.min x (current_min + x) in
      let global_min' := Z.min global_min current_min' in
      min_subarray_sum_aux xs current_min' global_min'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_subarray_sum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [50%Z; -50%Z; 100%Z; -100%Z; 50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z] = -100%Z.
Proof. reflexivity. Qed.