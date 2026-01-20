Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (min_so_far : Z) : Z :=
  match nums with
  | [] => min_so_far
  | x :: xs =>
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min min_so_far new_current in
      minSubArraySum_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_case_1: minSubArraySum [-5; -1; 3; -2; -4; 6; -1; -1] = -9.
Proof. reflexivity. Qed.