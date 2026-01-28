Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let aux (acc : Z * Z) (n : Z) :=
        let (current_min, global_min) := acc in
        let new_current := Z.min n (current_min + n) in
        let new_global := Z.min global_min new_current in
        (new_current, new_global)
      in
      snd (fold_left aux xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; 1%Z; -1%Z; 1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -3%Z.
Proof. reflexivity. Qed.