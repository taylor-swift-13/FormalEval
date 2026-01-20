Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (glob : Z) : Z :=
      match l with
      | [] => glob
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let glob' := Z.min glob curr' in
        aux ys curr' glob'
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum: min_sub_array_sum [1; -6; -3; -4; 5; -6; 7; -8; 9; 4; 8; -2; 2; 9] = -15.
Proof. reflexivity. Qed.