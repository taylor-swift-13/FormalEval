Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let aux (acc : Z * Z) (y : Z) :=
      let (curr, glob) := acc in
      let curr' := Z.min y (curr + y) in
      let glob' := Z.min glob curr' in
      (curr', glob')
    in
    let (final_curr, final_glob) := fold_left aux xs (x, x) in
    final_glob
  end.

Example test_minSubArraySum: minSubArraySum [-2%Z; 6%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; -3%Z; -3%Z; 2%Z; -1%Z; 4%Z] = -14%Z.
Proof. reflexivity. Qed.