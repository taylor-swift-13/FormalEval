Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let f (acc : Z * Z) (n : Z) :=
      let (curr, glob) := acc in
      let curr' := Z.min n (curr + n) in
      let glob' := Z.min glob curr' in
      (curr', glob')
    in
    snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; -4%Z; -9%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -10%Z; -10%Z; -10%Z] = -48%Z.
Proof. reflexivity. Qed.