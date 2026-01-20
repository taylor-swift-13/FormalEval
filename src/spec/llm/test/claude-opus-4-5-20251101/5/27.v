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

Example test_intersperse_multiple : intersperse_spec [0; 0; 0; -1] 7 [0; 7; 0; 7; 0; 7; -1].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.