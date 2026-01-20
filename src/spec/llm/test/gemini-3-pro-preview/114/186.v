Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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

Definition min_subarray_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_subarray_sum_aux xs x x
  end.

Example test_min_subarray_sum:
  min_subarray_sum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; -50%Z; 100%Z; -100%Z; -50%Z; 100%Z; -100%Z; -100000%Z; 50%Z; -51%Z; 100%Z; 50%Z] = -100261%Z.
Proof.
  reflexivity.
Qed.