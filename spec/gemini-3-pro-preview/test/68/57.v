Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
    let fix aux (rem : list Z) (i : Z) (min_val : Z) (min_idx : Z) : list Z :=
      match rem with
      | [] => [min_val; min_idx]
      | x :: xs =>
        if x <? min_val then aux xs (i + 1) x i
        else aux xs (i + 1) min_val min_idx
      end
    in aux t 1 h 0
  end.

Example test_case: solution [2%Z; 5%Z; 4%Z; 11%Z; 7%Z; 9%Z; 11%Z; 2%Z; 9%Z; 9%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.