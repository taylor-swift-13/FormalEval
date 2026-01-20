Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
    let fix aux (rest : list Z) (min_val : Z) (min_idx : Z) (curr_idx : Z) :=
      match rest with
      | [] => [min_val; min_idx]
      | y :: ys =>
        if y <? min_val then aux ys y curr_idx (curr_idx + 1)
        else aux ys min_val min_idx (curr_idx + 1)
      end
    in aux xs x 0 1
  end.

Example test_case_1: solution [6%Z; 5%Z; 2%Z; 0%Z; 8%Z; 11%Z; 1%Z; 101%Z; 5%Z; 7%Z; 8%Z; 11%Z] = [0%Z; 3%Z].
Proof. reflexivity. Qed.