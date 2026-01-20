Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      fst (fold_left (fun (acc : Z * Z) (n : Z) =>
                        let (min_so_far, current_min) := acc in
                        let current_min' := Z.min n (current_min + n) in
                        (Z.min min_so_far current_min', current_min'))
                      xs (x, x))
  end.

Example test_minSubArraySum : minSubArraySum [-10; -9; -8; -7; -6; -5; -7; -4; -3; -2; -1] = -62.
Proof. reflexivity. Qed.