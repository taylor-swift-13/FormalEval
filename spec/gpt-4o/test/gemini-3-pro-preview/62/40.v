Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [2; -2; 0; 0; 0; 5] [-2; 0; 0; 0; 25].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.