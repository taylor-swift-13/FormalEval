Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix aux (l : list Z) (curr_min : Z) (global_min : Z) : Z :=
        match l with
        | [] => global_min
        | h :: t =>
            let new_curr := Z.min h (curr_min + h) in
            let new_global := Z.min global_min new_curr in
            aux t new_curr new_global
        end
      in aux xs x x
  end.

Example test_minSubArraySum: minSubArraySum [1; -2; -4; -6; 8; -8; 9; 4; -3; 2; -1] = -12.
Proof.
  compute.
  reflexivity.
Qed.