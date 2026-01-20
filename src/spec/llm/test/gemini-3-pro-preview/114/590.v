Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(min_so_far, _) :=
        fold_left (fun (acc : Z * Z) (y : Z) =>
          let '(g, c) := acc in
          let c' := Z.min y (c + y) in
          (Z.min g c', c')
        ) xs (x, x)
      in min_so_far
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [1%Z; -2%Z; 3%Z; 100%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; -3%Z; 2%Z; 20%Z; -1%Z; 5%Z; -3%Z; -2%Z] = -8%Z.
Proof.
  reflexivity.
Qed.