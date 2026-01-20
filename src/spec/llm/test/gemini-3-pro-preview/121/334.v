Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_odd_at_even_pos (lst : list Z) : Z :=
  match lst with
  | [] => 0
  | [x] => if Z.odd x then x else 0
  | x :: _ :: xs => (if Z.odd x then x else 0) + sum_odd_at_even_pos xs
  end.

Definition solution_spec (lst : list Z) (res : Z) : Prop :=
  res = sum_odd_at_even_pos lst.

Example test_case : solution_spec [86; 2; 3; 65; 5; 6; 42; 53; 77; 9; 10] 85.
Proof.
  unfold solution_spec.
  simpl.
  reflexivity.
Qed.