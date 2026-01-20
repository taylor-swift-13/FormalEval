Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let f (acc : Z * Z) (n : Z) :=
      let (curr_min, global_min) := acc in
      let new_curr := Z.min n (curr_min + n) in
      let new_global := Z.min global_min new_curr in
      (new_curr, new_global)
    in
    let (_, res) := fold_left f xs (x, x) in
    res
  end.

Example test_minSubArraySum:
  minSubArraySum [-5; -1; -2; -2; -4; 6; -1; -1] = -14.
Proof. reflexivity. Qed.