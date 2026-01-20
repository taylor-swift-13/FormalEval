Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let step (acc : Z * Z) (y : Z) :=
        let (curr, glob) := acc in
        let curr' := Z.min y (curr + y) in
        let glob' := Z.min glob curr' in
        (curr', glob')
      in
      snd (fold_left step xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [1; -1; -1; 1] = -2.
Proof.
  reflexivity.
Qed.