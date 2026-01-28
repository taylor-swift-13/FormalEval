Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [2; 0; 3; 0; 1; 1; 1; 0; -2; 5; 6; 0; 0] [0; 6; 0; 4; 5; 6; 0; -16; 45; 60; 0; 0].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.