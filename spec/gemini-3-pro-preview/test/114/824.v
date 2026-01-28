Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    snd (fold_left (fun (acc : Z * Z) (y : Z) =>
             let (curr, glob) := acc in
             let curr' := Z.min y (curr + y) in
             (curr', Z.min glob curr'))
           xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [-3; 1; -2; 5; -6; 4; -3; 2; -1; -1] = -6.
Proof. reflexivity. Qed.