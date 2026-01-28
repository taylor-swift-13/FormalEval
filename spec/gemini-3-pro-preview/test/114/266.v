Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minSubArraySum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let (final_curr, final_glob) :=
        fold_left (fun (acc : Z * Z) (y : Z) =>
          let (curr, glob) := acc in
          let new_curr := Z.min y (curr + y) in
          let new_glob := Z.min glob new_curr in
          (new_curr, new_glob)
        ) xs (x, x)
      in final_glob
  end.

Example test_minSubArraySum_new:
  minSubArraySum [1%Z; -2%Z; 3%Z; -5%Z; 5%Z; -6%Z; 7%Z; 5%Z; -8%Z; 9%Z; 4%Z; 2%Z; 2%Z; 70%Z; -1%Z; 5%Z] = -8%Z.
Proof.
  compute. reflexivity.
Qed.