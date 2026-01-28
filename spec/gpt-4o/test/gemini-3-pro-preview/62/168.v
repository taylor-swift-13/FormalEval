Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [63; -1; 0; 0; 63; 0; 0; 0; 63; 0; 0; 0; 1] [-1; 0; 0; 252; 0; 0; 0; 504; 0; 0; 0; 12].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.