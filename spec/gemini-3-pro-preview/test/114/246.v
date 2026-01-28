Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
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
        let new_curr := Z.min y (curr + y) in
        aux ys new_curr (Z.min min_so_far new_curr)
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum:
  min_sub_array_sum [-100%Z; 49%Z; -10%Z; -50%Z; 100%Z; 50%Z; -50%Z; -100%Z; -50%Z; 100%Z; -100%Z; 50%Z; -50%Z; 100%Z; -100%Z; -100000%Z; -51%Z; 100%Z] = -100251%Z.
Proof. reflexivity. Qed.