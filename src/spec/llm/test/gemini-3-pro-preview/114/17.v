Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint min_sub_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
      let next_current := Z.min x (current_min + x) in
      let next_global := Z.min global_min next_current in
      min_sub_aux xs next_current next_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => min_sub_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-2; -5; -8; -3; -1; -2; -4] = -25.
Proof. reflexivity. Qed.