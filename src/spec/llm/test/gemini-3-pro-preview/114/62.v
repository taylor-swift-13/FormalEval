Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(final_min, final_global) :=
        fold_left (fun '(curr, glob) y =>
          let curr' := Z.min y (curr + y) in
          let glob' := Z.min glob curr' in
          (curr', glob')
        ) xs (x, x)
      in final_global
  end.

Example test_minSubArraySum : minSubArraySum [-2%Z; -5%Z; -8%Z; -3%Z; -1%Z; -2%Z; -4%Z; -10%Z; -3%Z] = -38%Z.
Proof. reflexivity. Qed.