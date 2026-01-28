Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [5; 3; 1; 0; -1; -3; -5; -7; -9] [3; 2; 0; -4; -15; -30; -49; -72].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.