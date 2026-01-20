Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let f (acc : Z * Z) (y : Z) :=
      let (curr, min_so_far) := acc in
      let new_curr := Z.min y (curr + y) in
      let new_min := Z.min min_so_far new_curr in
      (new_curr, new_min)
    in
    snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum_2 : minSubArraySum [1; -1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1] = -2.
Proof.
  compute.
  reflexivity.
Qed.