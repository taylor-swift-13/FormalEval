Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      let fix aux (rem : list Z) (i : Z) (min_v : Z) (min_i : Z) :=
        match rem with
        | [] => [min_v; min_i]
        | y :: ys =>
            if y <? min_v then aux ys (i + 1) y i
            else aux ys (i + 1) min_v min_i
        end
      in aux xs 1 x 0
  end.

Example test_case: solution [6; 4; 2; 0; 8; 10; 4; 8] = [0; 3].
Proof.
  reflexivity.
Qed.