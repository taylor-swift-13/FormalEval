Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let solve := fold_left (fun (acc : Z * Z) (y : Z) =>
                   let '(global_min, current_min) := acc in
                   let current_min' := Z.min y (current_min + y) in
                   let global_min' := Z.min global_min current_min' in
                   (global_min', current_min'))
                 xs (x, x) in
    fst solve
  end.

Example test_min_sub_array_sum : minSubArraySum [-2; 1; -4; 6; -7; -4; -5; 1; -4] = -19.
Proof.
  compute.
  reflexivity.
Qed.