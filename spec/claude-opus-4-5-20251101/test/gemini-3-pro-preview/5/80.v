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

Example test_intersperse_1 : intersperse_spec [5%Z; 15%Z; 63%Z; 2%Z; -2%Z; 5%Z; 9%Z; 100%Z; 5%Z; -9%Z] 8%Z [5%Z; 8%Z; 15%Z; 8%Z; 63%Z; 8%Z; 2%Z; 8%Z; -2%Z; 8%Z; 5%Z; 8%Z; 9%Z; 8%Z; 100%Z; 8%Z; 5%Z; 8%Z; -9%Z].
Proof.
  unfold intersperse_spec.
  simpl.
  reflexivity.
Qed.