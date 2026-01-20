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
        let curr' := Z.min y (curr + y) in
        aux ys curr' (Z.min min_so_far curr')
      end
    in aux xs x x
  end.

Example test_min_sub_array_sum: min_sub_array_sum [-10%Z; -9%Z; -7%Z; -7%Z; -6%Z; -5%Z; -50000%Z; -2%Z; -2%Z; -8%Z] = -50056%Z.
Proof. reflexivity. Qed.