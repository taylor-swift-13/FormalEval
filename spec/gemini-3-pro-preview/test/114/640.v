Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let f (acc : Z * Z) (y : Z) :=
        let (current_min, global_min) := acc in
        let new_current := Z.min y (current_min + y) in
        let new_global := Z.min global_min new_current in
        (new_current, new_global)
      in
      snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 90%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -2%Z.
Proof. reflexivity. Qed.