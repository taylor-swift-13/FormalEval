Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_min_idx (l : list Z) (current_min : Z) (next_idx : Z) (best_idx : Z) : (Z * Z) :=
  match l with
  | [] => (current_min, best_idx)
  | x :: xs =>
      if (x <? current_min) then
        find_min_idx xs x (next_idx + 1) next_idx
      else
        find_min_idx xs current_min (next_idx + 1) best_idx
  end.

Definition solution (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
      let (m, i) := find_min_idx xs x 1 0 in
      [m; i]
  end.

Example test_case_1 : solution [2; 4; 7; 6; 8; 6] = [2; 0].
Proof.
  reflexivity.
Qed.