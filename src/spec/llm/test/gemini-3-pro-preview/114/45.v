Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let process (acc : Z * Z) (n : Z) :=
      let (curr_min, global_min) := acc in
      let curr_min' := Z.min n (curr_min + n) in
      let global_min' := Z.min global_min curr_min' in
      (curr_min', global_min')
    in
    snd (fold_left process xs (x, x))
  end.

Example example_minSubArraySum : minSubArraySum [-5; 2; 4; -1; 3; 3; 5; -4; 1; -2] = -5.
Proof.
  reflexivity.
Qed.