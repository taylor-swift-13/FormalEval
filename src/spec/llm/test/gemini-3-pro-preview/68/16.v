Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint find_min_helper (l : list Z) (min_val : Z) (min_idx : Z) (curr_idx : Z) : list Z :=
  match l with
  | [] => [min_val; min_idx]
  | x :: xs =>
      if x <? min_val then
        find_min_helper xs x curr_idx (curr_idx + 1)
      else
        find_min_helper xs min_val min_idx (curr_idx + 1)
  end.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => find_min_helper xs x 0 1
  end.

Example test_case: solution [6%Z; 4%Z; 2%Z; 0%Z; 8%Z; 10%Z; 1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 11%Z] = [0%Z; 3%Z].
Proof. reflexivity. Qed.