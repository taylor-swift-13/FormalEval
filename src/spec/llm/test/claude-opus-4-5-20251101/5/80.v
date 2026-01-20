Require Import List.
Require Import ZArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint intersperse_spec_aux (numbers : list Z) (delimiter : Z) : list Z :=
  match numbers with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: delimiter :: intersperse_spec_aux xs delimiter
  end.

Definition intersperse_spec (numbers : list Z) (delimiter : Z) (result : list Z) : Prop :=
  result = intersperse_spec_aux numbers delimiter.

Example test_intersperse_long : intersperse_spec [5; 15; 63; 2; -2; 5; 9; 100; 5; -9] 8 [5; 8; 15; 8; 63; 8; 2; 8; -2; 8; 5; 8; 9; 8; 100; 8; 5; 8; -9].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.