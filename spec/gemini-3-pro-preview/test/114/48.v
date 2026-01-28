Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | x :: xs =>
      let '(final_min, _) :=
        fold_left (fun acc y =>
          let '(g_min, c_min) := acc in
          let c_min' := Z.min y (c_min + y) in
          let g_min' := Z.min g_min c_min' in
          (g_min', c_min')
        ) xs (x, x)
      in final_min
  end.

Example test_min_sub_array_sum: min_sub_array_sum [-3; -2; -3; -4] = -12.
Proof. reflexivity. Qed.