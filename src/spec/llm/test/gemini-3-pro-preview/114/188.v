Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let f (acc : Z * Z) (x : Z) :=
      let (current_min, global_min) := acc in
      let new_current := Z.min x (current_min + x) in
      let new_global := Z.min global_min new_current in
      (new_current, new_global)
    in
    snd (fold_left f ns (n, n))
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; 10%Z; 4%Z; 1%Z; 2%Z; 70%Z; -1%Z] = -8%Z.
Proof. reflexivity. Qed.