Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fix iter (l : list Z) (curr : Z) (min_so_far : Z) : Z :=
        match l with
        | [] => min_so_far
        | y :: ys =>
            let curr' := Z.min y (curr + y) in
            let min_so_far' := Z.min min_so_far curr' in
            iter ys curr' min_so_far'
        end
      in iter xs x x
  end.

Example test_minSubArraySum:
  minSubArraySum [-2; 1; -4; -7; -4; -5; 1; -4] = -24.
Proof. reflexivity. Qed.