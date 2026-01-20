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
  min_sub_array_sum [-100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; 50%Z; -51%Z; 100%Z; 100%Z] = -101%Z.
Proof. reflexivity. Qed.