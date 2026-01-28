Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
    let fix aux (rem : list Z) (min_val : Z) (min_idx : Z) (curr_idx : Z) :=
      match rem with
      | [] => [min_val; min_idx]
      | x :: xs =>
        if x <? min_val then aux xs x curr_idx (curr_idx + 1)
        else aux xs min_val min_idx (curr_idx + 1)
      end
    in aux t h 0 1
  end.

Example test_case: solution [0; 2; 3; 6; 8; 10; 31; 3; 5; 7; 9; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31; 33; 35; 37; 39; 9; 37; 33] = [0; 0].
Proof. compute. reflexivity. Qed.