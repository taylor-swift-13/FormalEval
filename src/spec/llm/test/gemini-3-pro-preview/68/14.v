Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_idx (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
      let fix aux (lst : list Z) (idx : Z) (min_val : Z) (min_pos : Z) : list Z :=
        match lst with
        | [] => [min_val; min_pos]
        | x :: xs =>
            if x <? min_val then aux xs (idx + 1) x idx
            else aux xs (idx + 1) min_val min_pos
        end
      in aux t 1 h 0
  end.

Example test_min_idx: min_idx [6; 4; 2; 0; 8; 10] = [0; 3].
Proof. reflexivity. Qed.