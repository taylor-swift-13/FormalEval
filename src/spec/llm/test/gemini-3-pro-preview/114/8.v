Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let f (acc : Z * Z) (y : Z) :=
        let (curr, glob) := acc in
        let curr' := Z.min y (curr + y) in
        let glob' := Z.min glob curr' in
        (curr', glob')
      in
      snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [10; 11; 13; 8; 3; 4] = 3.
Proof.
  reflexivity.
Qed.