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

Example test_intersperse_1 : intersperse_spec [-48; 4; 1; 2; 3] 3 [-48; 3; 4; 3; 1; 3; 2; 3; 3].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.