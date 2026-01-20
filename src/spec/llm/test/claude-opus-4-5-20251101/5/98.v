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

Example test_intersperse_multiple : intersperse_spec [7; 3; 6; 8; 4; 2; 2] 10 [7; 10; 3; 10; 6; 10; 8; 10; 4; 10; 2; 10; 2].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.