Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint solve_aux (l : list Z) (idx : Z) (min_v : Z) (min_i : Z) : list Z :=
  match l with
  | [] => [min_v; min_i]
  | x :: xs =>
      if x <? min_v then solve_aux xs (idx + 1) x idx
      else solve_aux xs (idx + 1) min_v min_i
  end.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs => solve_aux xs 1 x 0
  end.

Example test_case: solution [10%Z; 14%Z; 20%Z; 20%Z] = [10%Z; 0%Z].
Proof. reflexivity. Qed.