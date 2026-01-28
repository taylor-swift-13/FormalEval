Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
    let fix aux (rem : list Z) (min_v : Z) (min_i : Z) (curr_i : Z) : list Z :=
      match rem with
      | [] => [min_v; min_i]
      | h :: t =>
        if h <? min_v then aux t h curr_i (curr_i + 1)
        else aux t min_v min_i (curr_i + 1)
      end
    in aux xs x 0 1
  end.

Example test_case: solution [0%Z; 3%Z; 9%Z; 9%Z; 7%Z; 7%Z] = [0%Z; 0%Z].
Proof.
  reflexivity.
Qed.