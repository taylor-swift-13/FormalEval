Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
    let fix aux (rest : list Z) (i : Z) (min_v : Z) (min_i : Z) : list Z :=
      match rest with
      | [] => [min_v; min_i]
      | y :: ys =>
        if y <? min_v then aux ys (i + 1) y i
        else aux ys (i + 1) min_v min_i
      end
    in aux xs 1 x 0
  end.

Example test_case: solve [7; 9; 23; 5; 3; 11; 13; 15; 17; 19; 21; 22; 31; 25; 27; 29; 31; 33; 11; 34; 39; 39; 4; 2; 7; 21] = [2; 23].
Proof.
  reflexivity.
Qed.