Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  let fix aux (lst : list Z) (idx : Z) (min_val : Z) (min_idx : Z) : list Z :=
    match lst with
    | [] => [min_val; min_idx]
    | x :: xs => if x <? min_val then aux xs (idx + 1) x idx
                 else aux xs (idx + 1) min_val min_idx
    end
  in
  match l with
  | [] => []
  | x :: xs => aux xs 1 x 0
  end.

Example test_case_new : solve [0; 2; 4; 6; 8; 10; 3; 5; 9; 11; 13; 15; 17; 19; 21; 23; 25; 27; 32; 31; 33; 9; 35; 9; 39; 39] = [0; 0].
Proof.
  reflexivity.
Qed.