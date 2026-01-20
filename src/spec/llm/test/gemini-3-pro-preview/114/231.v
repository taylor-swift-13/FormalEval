Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    fst (fold_left (fun (acc : Z * Z) (y : Z) =>
      let (g, c) := acc in
      let c' := Z.min y (c + y) in
      (Z.min g c', c')) xs (x, x))
  end.

Example test_minSubArraySum: minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -100%Z; -1%Z; 1%Z; 2%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z] = -101%Z.
Proof.
  compute. reflexivity.
Qed.