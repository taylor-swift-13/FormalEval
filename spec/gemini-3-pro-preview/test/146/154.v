Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint is_non_decreasing (l : list Z) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      match xs with
      | [] => true
      | y :: ys => (x <=? y) && is_non_decreasing xs
      end
  end.

Definition solution (l : list Z) : Z :=
  if is_non_decreasing l then 1 else 0.

Example test_case: solution [100; 102; 102; 103; 104] = 1.
Proof.
  unfold solution.
  simpl.
  reflexivity.
Qed.