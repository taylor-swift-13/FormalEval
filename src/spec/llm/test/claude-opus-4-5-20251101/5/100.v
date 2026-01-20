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

Example test_intersperse_long : intersperse_spec [15; 63; 2; -2; 5; -93; 100; 5; -9] 9 [15; 9; 63; 9; 2; 9; -2; 9; 5; 9; -93; 9; 100; 9; 5; 9; -9].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.