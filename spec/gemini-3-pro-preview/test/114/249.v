Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let '(min_global, _) :=
      fold_left (fun '(g, c) y =>
        let c' := Z.min y (c + y) in
        (Z.min g c', c')
      ) xs (x, x)
    in min_global
  end.

Example test_minSubArraySum:
  minSubArraySum [1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -1%Z; 1%Z; -100%Z; -1%Z; 1%Z; -50%Z; 1%Z; -1%Z; -3%Z; 1%Z; -1%Z; -1%Z] = -154%Z.
Proof. reflexivity. Qed.