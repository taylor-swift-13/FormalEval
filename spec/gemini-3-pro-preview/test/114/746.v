Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (l : list Z) (current_min : Z) (global_min : Z) : Z :=
  match l with
  | [] => global_min
  | x :: xs =>
    let current_min' := Z.min x (current_min + x) in
    let global_min' := Z.min global_min current_min' in
    minSubArraySum_aux xs current_min' global_min'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum_2:
  minSubArraySum [-10; -9; -8; -1; -7; -6; -5; -4; -3; -2; 100000; -1; -9] = -55.
Proof.
  simpl. reflexivity.
Qed.