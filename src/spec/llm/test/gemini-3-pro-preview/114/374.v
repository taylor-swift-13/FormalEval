Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
    let fix aux (l : list Z) (curr : Z) (min_so_far : Z) : Z :=
      match l with
      | [] => min_so_far
      | y :: ys =>
        let curr' := Z.min y (curr + y) in
        let min_so_far' := Z.min min_so_far curr' in
        aux ys curr' min_so_far'
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [1; -1; 1; -1; -99; 0; 1; -1; 1; -1; -6; 1; -2; 1; -1; 1; 1; -80; 30; -1; 1; -1; 1; -1; 1; 1; -1; 1; -1; 1; -1; 1; -1] = -185.
Proof.
  compute. reflexivity.
Qed.