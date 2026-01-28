Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
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

Example test_min_sub_array_sum: min_sub_array_sum [1%Z; -2%Z; 3%Z; 5%Z; -6%Z; 7%Z; 9%Z; 4%Z; 4%Z; -7%Z; -80%Z; 6%Z; 2%Z; -1%Z; -6%Z] = -87%Z.
Proof. compute. reflexivity. Qed.