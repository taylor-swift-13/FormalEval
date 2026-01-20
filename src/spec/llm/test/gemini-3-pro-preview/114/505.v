Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_sub_array_sum (nums : list Z) : Z :=
  match nums with
  | [] => 0
  | n :: ns =>
    let fix aux (l : list Z) (current_min global_min : Z) : Z :=
      match l with
      | [] => global_min
      | x :: xs =>
        let new_current := Z.min x (current_min + x) in
        let new_global := Z.min global_min new_current in
        aux xs new_current new_global
      end
    in aux ns n n
  end.

Example test_min_sub_array_sum: min_sub_array_sum [1; -2; 1; -1; -1; 1; -1; -99999; 1; -1; 1; -1; 1; -1] = -100002.
Proof. reflexivity. Qed.