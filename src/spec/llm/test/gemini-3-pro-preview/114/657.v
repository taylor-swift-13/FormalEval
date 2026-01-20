Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let f (acc : Z * Z) (y : Z) :=
      let (curr, total) := acc in
      let curr' := Z.min y (curr + y) in
      let total' := Z.min total curr' in
      (curr', total')
    in
    snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [100000; -50000; 50000; -100000; 100000; -50000; 50000; 100000; -50000; 50000; -100000; 100000; -50000; 50000; -100000; 100000; -50000; 50000; -100000] = -100000.
Proof. reflexivity. Qed.