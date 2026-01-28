From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let '(curr, min_so_far) := fold_left (fun acc y =>
                                           let '(c, m) := acc in
                                           let c' := Z.min y (c + y) in
                                           (c', Z.min m c'))
                                         xs (x, x) in
    min_so_far
  end.

Example test_minSubArraySum: minSubArraySum [-1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; -1] = -2.
Proof. reflexivity. Qed.