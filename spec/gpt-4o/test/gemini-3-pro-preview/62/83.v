Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [7; 3; -1; 0; 6; -1; 0] [3; -2; 0; 24; -5; 0].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.