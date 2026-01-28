Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let step (acc : Z * Z) (n : Z) :=
        let (curr, global) := acc in
        let curr' := Z.min n (curr + n) in
        (curr', Z.min global curr')
      in
      snd (fold_left step xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -3%Z; 4%Z; -1%Z; 2%Z; 1%Z; -5%Z; 4%Z] = -5%Z.
Proof. reflexivity. Qed.