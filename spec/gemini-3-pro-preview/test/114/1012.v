Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let fold_fun (acc : Z * Z) (n : Z) :=
        let (current_min, global_min) := acc in
        let new_current_min := Z.min n (current_min + n) in
        let new_global_min := Z.min global_min new_current_min in
        (new_current_min, new_global_min)
      in
      snd (fold_left fold_fun xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [10; -20; 30; -21; -40; 50; -60; 50000; 70; -21; -80; 90; -100; 10; 10] = -111.
Proof.
  reflexivity.
Qed.