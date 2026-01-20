Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let f (acc : Z * Z) (n : Z) :=
        let (curr, total) := acc in
        let new_curr := Z.min n (curr + n) in
        let new_total := Z.min total new_curr in
        (new_curr, new_total)
      in
      snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum_1:
  minSubArraySum [-8; -9; 20; -30; 21; 40; -50; 80; 80; -90; 100; 20; 80] = -90.
Proof.
  compute. reflexivity.
Qed.