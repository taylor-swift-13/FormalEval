Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix iter (l : list Z) (curr min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let min_so_far' := Z.min min_so_far curr' in
        iter ys curr' min_so_far'
      end
    in iter xs x x
  end.

Example test_minSubArraySum: minSubArraySum [-70; -1; 1; 0; -1; -8; 1; -1; 1; -1; 2; -1; -1] = -79.
Proof. reflexivity. Qed.