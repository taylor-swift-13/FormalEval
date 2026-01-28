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
      (curr', Z.min glob curr')
    in
    snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum:
  minSubArraySum [11%Z; 2%Z; -2%Z; 3%Z; 1%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -10%Z; -10%Z; -8%Z] = -28%Z.
Proof.
  reflexivity.
Qed.