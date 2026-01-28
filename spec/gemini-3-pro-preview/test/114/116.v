Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let f (acc : Z * Z) (y : Z) :=
      let (curr, glob) := acc in
      let curr' := Z.min y (curr + y) in
      (curr', Z.min glob curr')
    in
    snd (fold_left f xs (x, x))
  end.

Example test_minSubArraySum : minSubArraySum [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; 4%Z; -3%Z; 2%Z; -1%Z] = (-8)%Z.
Proof. reflexivity. Qed.