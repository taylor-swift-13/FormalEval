Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint find_min_idx_aux (l : list Z) (idx : Z) (min_val : Z) (min_idx : Z) : list Z :=
  match l with
  | [] => [min_val; min_idx]
  | x :: xs => 
      if x <? min_val then
        find_min_idx_aux xs (idx + 1) x idx
      else
        find_min_idx_aux xs (idx + 1) min_val min_idx
  end.

Definition human_eval (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => find_min_idx_aux xs 1 x 0
  end.

Example test_case: human_eval [7; 2; 4; 6; 8; 11; 11] = [2; 1].
Proof.
  reflexivity.
Qed.