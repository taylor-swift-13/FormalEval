Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      let fix aux (rest : list Z) (idx : Z) (min_val : Z) (min_idx : Z) : list Z :=
        match rest with
        | [] => [min_val; min_idx]
        | y :: ys =>
            if y <? min_val then aux ys (idx + 1) y idx
            else aux ys (idx + 1) min_val min_idx
        end
      in aux xs 1 x 0
  end.

Example test_case_1: solution [0%Z; 2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 1%Z; 3%Z; 5%Z; 6%Z; 9%Z; 9%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.