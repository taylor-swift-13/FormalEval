Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
      let fix aux (xs : list Z) (min_val : Z) (min_idx : Z) (curr_idx : Z) :=
        match xs with
        | [] => [min_val; min_idx]
        | y :: ys =>
            if y <? min_val then aux ys y curr_idx (curr_idx + 1)
            else aux ys min_val min_idx (curr_idx + 1)
        end
      in aux t h 0 1
  end.

Example test_case: solution [2%Z; 2%Z; 5%Z; 10%Z; 7%Z; 9%Z; 11%Z; 2%Z; 9%Z; 9%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.