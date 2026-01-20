Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_subarray_aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
  match l with
  | [] => global_min
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min global_min new_current in
      min_subarray_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_subarray_aux xs x x
  end.

Example test_case_1: minSubArraySum [-100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; 2%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z] = -100%Z.
Proof. reflexivity. Qed.