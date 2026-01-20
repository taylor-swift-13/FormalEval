Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
    let fix aux (l' : list Z) (i : Z) (curr_min : Z) (curr_idx : Z) : list Z :=
      match l' with
      | [] => [curr_min; curr_idx]
      | h :: t =>
        if h <? curr_min
        then aux t (i + 1) h i
        else aux t (i + 1) curr_min curr_idx
      end
    in aux xs 1 x 0
  end.

Example test_case: solution [202%Z; 2%Z; 5%Z; 10%Z; 7%Z; 9%Z; 11%Z; 2%Z; 9%Z; 9%Z] = [2%Z; 1%Z].
Proof.
  reflexivity.
Qed.