Require Import List.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1%nat (length xs - 1)%nat).

Example test_derivative : derivative_spec [7; -1; 0; -1; 0] [-1; 0; -3; 0].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.