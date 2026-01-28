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

Example test_minSubArraySum: minSubArraySum [-8%Z; -9%Z; -30%Z; 40%Z; -50%Z; 60%Z; 80%Z; -70%Z; 80%Z; -90%Z; 100%Z; 100%Z] = -90%Z.
Proof. reflexivity. Qed.