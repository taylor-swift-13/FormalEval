Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
    let fix aux (l : list Z) (min_val : Z) (min_idx : Z) (curr_idx : Z) : list Z :=
      match l with
      | [] => [min_val; min_idx]
      | h :: t =>
        if h <? min_val then aux t h curr_idx (curr_idx + 1)
        else aux t min_val min_idx (curr_idx + 1)
      end
    in aux xs x 0 1
  end.

Example test_case: solve [4; 0; 7; 3; 2; 3; 6; 8; 10; 2] = [0; 1].
Proof.
  reflexivity.
Qed.