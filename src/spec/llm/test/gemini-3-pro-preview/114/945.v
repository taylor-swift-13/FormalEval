Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let '(min_so_far, current_min) :=
      fold_left (fun '(g_min, c_min) n =>
                   let c_min' := Z.min n (c_min + n) in
                   (Z.min g_min c_min', c_min'))
                xs (x, x)
    in min_so_far
  end.

Example test_case_1: minSubArraySum [1; -3; -4; 5; 1; -6; 7; -8; 9; 4; -2; 2; 9] = -8.
Proof. reflexivity. Qed.