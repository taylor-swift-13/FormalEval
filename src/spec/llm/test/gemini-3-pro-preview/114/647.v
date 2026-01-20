Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix helper (l : list Z) (current_min global_min : Z) : Z :=
        match l with
        | [] => global_min
        | y :: ys =>
            let current_min' := Z.min y (current_min + y) in
            let global_min' := Z.min global_min current_min' in
            helper ys current_min' global_min'
        end
      in helper xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-9; -10; -30; -30; 40; -50; 60; 81; -90; 100] = -90.
Proof.
  reflexivity.
Qed.