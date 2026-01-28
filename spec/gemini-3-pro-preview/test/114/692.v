Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let step (acc : Z * Z) (n : Z) :=
      let (current_min, global_min) := acc in
      let current_min' := Z.min n (current_min + n) in
      let global_min' := Z.min global_min current_min' in
      (current_min', global_min')
    in
    snd (fold_left step xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [10%Z; -20%Z; 30%Z; -40%Z; 50%Z; 70%Z; -80%Z; 90%Z; -100%Z; 50%Z] = -100%Z.
Proof.
  reflexivity.
Qed.