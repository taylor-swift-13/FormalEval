Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_aux (l : list Z) (idx : Z) (min_val : Z) (min_idx : Z) : Z * Z :=
  match l with
  | [] => (min_val, min_idx)
  | x :: xs =>
      if x <? min_val then
        find_min_aux xs (idx + 1) x idx
      else
        find_min_aux xs (idx + 1) min_val min_idx
  end.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      let (m, i) := find_min_aux xs 1 x 0 in
      [m; i]
  end.

Example test_case: solution [6; 4; 2; 0; 8; 10; 1; 3; 5; 7; 9; 11; 2] = [0; 3].
Proof.
  reflexivity.
Qed.