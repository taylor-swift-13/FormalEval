Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let f (acc : Z * Z) (y : Z) :=
      let (curr, min_so_far) := acc in
      let new_curr := Z.min y (curr + y) in
      (new_curr, Z.min min_so_far new_curr)
    in
    snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [1; -2; 3; -5; 5; -6; 7; 5; 9; 4; 2; 2; 70; -1; 5] = -6.
Proof.
  compute. reflexivity.
Qed.