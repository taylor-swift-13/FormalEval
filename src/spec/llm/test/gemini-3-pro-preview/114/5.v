Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let '(min_so_far, _) :=
      fold_left (fun acc y =>
        let '(min_global, current_min) := acc in
        let current_min' := Z.min y (current_min + y) in
        (Z.min min_global current_min', current_min')
      ) xs (x, x)
    in min_so_far
  end.

Example test_minSubArraySum: minSubArraySum [0; 10; 20; 1000000] = 0.
Proof.
  simpl.
  reflexivity.
Qed.