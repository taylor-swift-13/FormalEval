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

Example test_intersperse_basic : intersperse_spec [1%Z; 2%Z; 3%Z; 4%Z] 4%Z [1%Z; 4%Z; 2%Z; 4%Z; 3%Z; 4%Z; 4%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.