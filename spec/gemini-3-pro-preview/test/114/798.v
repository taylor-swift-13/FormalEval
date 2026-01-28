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
            let new_curr := Z.min y (curr + y) in
            let new_glob := Z.min glob new_curr in
            aux ys new_curr new_glob
        end
      in aux xs x x
  end.

Example test_min_sub_array_sum: min_sub_array_sum [-10%Z; -9%Z; -7%Z; -6%Z; -5%Z; -9%Z; -9%Z; -100%Z; -2%Z; -1%Z; -5%Z] = -163%Z.
Proof. reflexivity. Qed.