Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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
        aux ys curr' (Z.min glob curr')
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum: min_sub_array_sum [1; -1; 1; 1; -1; 1; -1; 1; 7; 2; -1] = -1.
Proof. reflexivity. Qed.