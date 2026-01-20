Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint minSubArraySum_aux (nums : list Z) (curr_min glob_min : Z) : Z :=
  match nums with
  | [] => glob_min
  | x :: xs =>
    let curr_min' := Z.min x (curr_min + x) in
    let glob_min' := Z.min glob_min curr_min' in
    minSubArraySum_aux xs curr_min' glob_min'
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs => minSubArraySum_aux xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [1; 2; 3; 4; 6; 6; 7; 8; 10; 10; 3; 10; 10; 10; 10; 11; 12; 13; 14; 15; 10] = 1.
Proof.
  simpl.
  reflexivity.
Qed.