Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
      let new_curr := Z.min x (curr_min + x) in
      let new_global := Z.min global_min new_curr in
      minSubArraySum_aux xs new_curr new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum_2:
  minSubArraySum [-1; 2; -3; 4; -5; 6; -7; 8; -7; -9; 10; -7] = -16.
Proof.
  vm_compute.
  reflexivity.
Qed.