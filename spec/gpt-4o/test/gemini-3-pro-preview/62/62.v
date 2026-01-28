Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [0; -1; 0; 0; 6; 0; 0; 0; 0; 7; 0; 1; 8; 6; 0; 0] [-1; 0; 0; 24; 0; 0; 0; 0; 63; 0; 11; 96; 78; 0; 0].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.