Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min (a b : Z) : Z := if a <? b then a else b.

Fixpoint minSubArraySum_aux (nums : list Z) (current_min : Z) (global_min : Z) : Z :=
  match nums with
  | [] => global_min
  | x :: xs =>
      let new_current := min x (current_min + x) in
      let new_global := min global_min new_current in
      minSubArraySum_aux xs new_current new_global
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1; -6; -3; -4; 5; -6; 7; -8; 9; 4; 8; -2; 2] = -15.
Proof. reflexivity. Qed.