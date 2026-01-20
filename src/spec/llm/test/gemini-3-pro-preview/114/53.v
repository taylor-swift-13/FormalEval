Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let f (acc : Z * Z) (y : Z) :=
        let (curr_min, glob_min) := acc in
        let new_curr := Z.min y (curr_min + y) in
        let new_glob := Z.min glob_min new_curr in
        (new_curr, new_glob)
      in
      snd (fold_left f xs (x, x))
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [3%Z; 2%Z; -5%Z; 4%Z; 2%Z; -3%Z; 2%Z; -1%Z] = -5%Z.
Proof. reflexivity. Qed.