Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let f (acc : Z * Z) (n : Z) :=
      let (curr, min_so_far) := acc in
      let new_curr := Z.min n (curr + n) in
      let new_min := Z.min min_so_far new_curr in
      (new_curr, new_min)
    in
    snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [-100%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; -50000%Z; -100%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; -51%Z; -100%Z; 100%Z] = -150361%Z.
Proof. reflexivity. Qed.