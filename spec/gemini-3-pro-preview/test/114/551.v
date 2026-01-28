Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let step (acc : Z * Z) (n : Z) :=
        let (curr, min_so_far) := acc in
        let curr' := Z.min n (curr + n) in
        (curr', Z.min min_so_far curr')
      in
      snd (fold_left step xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -2%Z; 1%Z; -1%Z; -1%Z; 1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z] = -4%Z.
Proof. reflexivity. Qed.