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

Example test_case : solution_spec [11; 22; 33; 1; 44; 65; 55; 66; 88; 56; 99; 0; 22; 33; 88] 198.
Proof.
  unfold solution_spec.
  simpl.
  reflexivity.
Qed.