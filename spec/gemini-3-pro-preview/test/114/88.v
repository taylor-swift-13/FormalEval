Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr_min : Z) (glob_min : Z) : Z :=
  match nums with
  | [] => glob_min
  | x :: xs =>
    let new_curr := Z.min x (curr_min + x) in
    let new_glob := Z.min glob_min new_curr in
    minSubArraySum_aux xs new_curr new_glob
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-2; -1; -4; 6; -7; 8; -5; -2] = -8.
Proof. reflexivity. Qed.