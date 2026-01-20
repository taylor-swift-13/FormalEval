Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    snd (fold_left (fun (acc : Z * Z) (n : Z) =>
             let (curr, glob) := acc in
             let curr' := Z.min n (curr + n) in
             let glob' := Z.min glob curr' in
             (curr', glob')) xs (x, x))
  end.

Example test_minSubArraySum : minSubArraySum [1; -2; 3; -4; 5; -6; 7; -8; 9; -10; -10; 3] = -20.
Proof. reflexivity. Qed.