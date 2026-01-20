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

Example test_intersperse_multiple : intersperse_spec [4; 1; 2; 3; 3; -5] 10000 [4; 10000; 1; 10000; 2; 10000; 3; 10000; 3; 10000; -5].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.