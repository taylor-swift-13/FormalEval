Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let '(final_curr, final_glob) :=
      fold_left (fun '(curr, glob) y =>
        let curr' := Z.min y (curr + y) in
        (curr', Z.min glob curr')
      ) xs (x, x)
    in final_glob
  end.

Example test_case : min_sub_array_sum [-1; 2; -3; 4; -5; 6; -7; 8; -9; 10; -7; 10] = -9.
Proof. reflexivity. Qed.