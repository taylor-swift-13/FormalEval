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
    let (_, res) := fold_left step xs (x, x) in
    res
  end.

Example test_case_1: minSubArraySum [-10; 50; -30; -5; 40; -50; 60; -70; 81; -2; 100] = -70.
Proof. reflexivity. Qed.