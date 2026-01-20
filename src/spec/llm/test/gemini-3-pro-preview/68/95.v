Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_aux (l : list Z) (idx : Z) (min_val : Z) (min_idx : Z) : list Z :=
  match l with
  | [] => [min_val; min_idx]
  | x :: xs => if x <? min_val then find_min_aux xs (idx + 1) x idx
               else find_min_aux xs (idx + 1) min_val min_idx
  end.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => find_min_aux xs 1 x 0
  end.

Example test_case: solution [6%Z; 4%Z; 2%Z; 0%Z; 8%Z; 10%Z; 6%Z] = [0%Z; 3%Z].
Proof.
  compute. reflexivity.
Qed.