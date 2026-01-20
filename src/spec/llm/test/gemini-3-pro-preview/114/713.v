Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let fix helper (l : list Z) (current_min : Z) (global_min : Z) : Z :=
      match l with
      | [] => global_min
      | x :: xs =>
        let new_current := Z.min x (current_min + x) in
        let new_global := Z.min global_min new_current in
        helper xs new_current new_global
      end
    in helper ns n n
  end.

Example test_min_sub_array_sum: min_sub_array_sum [1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1] = -1.
Proof. reflexivity. Qed.