Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      let fix aux (rest : list Z) (i : Z) (min_v : Z) (min_i : Z) : list Z :=
        match rest with
        | [] => [min_v; min_i]
        | y :: ys =>
            if y <? min_v then
              aux ys (i + 1) y i
            else
              aux ys (i + 1) min_v min_i
        end
      in aux xs 1 x 0
  end.

Example test_case: solution [2%Z; 4%Z; 7%Z; 6%Z; 8%Z; 8%Z; 8%Z; 8%Z] = [2%Z; 0%Z].
Proof.
  vm_compute.
  reflexivity.
Qed.