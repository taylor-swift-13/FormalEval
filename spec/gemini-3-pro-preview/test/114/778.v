Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let f (acc : Z * Z) (n : Z) :=
        let (current_min, global_min) := acc in
        let current_min' := Z.min n (current_min + n) in
        let global_min' := Z.min global_min current_min' in
        (current_min', global_min')
      in
      let (_, res) := fold_left f xs (x, x) in
      res
  end.

Example test_minSubArraySum:
  minSubArraySum [10; -20; 30; -40; 3; 50; 21; 70; -80; 90; -100; 10] = -100.
Proof. reflexivity. Qed.