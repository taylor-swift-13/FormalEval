Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let step (acc : Z * Z) (n : Z) :=
      let (curr, glob) := acc in
      let curr' := Z.min n (curr + n) in
      let glob' := Z.min glob curr' in
      (curr', glob')
    in
    snd (fold_left step xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [10; -20; 30; -40; 50; -60; 70; 11; -80; 60; 90; -100; 90] = -100.
Proof. reflexivity. Qed.