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

Example test_case : solution_spec [65; 10; 22; 4; 33; 44; 55; 76; 66; 77; 88; 22; 33] 186.
Proof.
  unfold solution_spec.
  simpl.
  reflexivity.
Qed.