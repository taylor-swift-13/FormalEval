Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min global_min new_current in
      minSubArraySum_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [2; 4; -1; 3; 5; -4; 1; 5; -2] = -4.
Proof. reflexivity. Qed.