Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let f (acc : Z * Z) (n : Z) :=
        let (current_min, global_min) := acc in
        let new_current := Z.min n (current_min + n) in
        (new_current, Z.min global_min new_current)
      in
      snd (fold_left f xs (x, x))
  end.

Example minSubArraySum_test:
  minSubArraySum [-8%Z; -1%Z; 2%Z; -3%Z; 4%Z; -5%Z; 3%Z; 6%Z; 8%Z; -9%Z; 10%Z] = -11%Z.
Proof.
  reflexivity.
Qed.