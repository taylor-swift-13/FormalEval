Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let (res, _) :=
      fold_left (fun (acc : Z * Z) (x : Z) =>
                   let (min_so_far, current_min) := acc in
                   let new_current_min := Z.min x (current_min + x) in
                   let new_min_so_far := Z.min min_so_far new_current_min in
                   (new_min_so_far, new_current_min))
                xs (x, x)
    in res
  end.

Example test_minSubArraySum: minSubArraySum [-5; -8; -3; -1; -2; -4; -1] = -24.
Proof. reflexivity. Qed.