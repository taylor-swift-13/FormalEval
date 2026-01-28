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

Example test_intersperse_full : intersperse_spec [-2; 5; 10; -5; 2] (-8) [-2; -8; 5; -8; 10; -8; -5; -8; 2].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.