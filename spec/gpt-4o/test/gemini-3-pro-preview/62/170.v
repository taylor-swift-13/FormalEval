Require Import List.
Require Import ZArith.
Require Import Nat.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1 (length xs - 1)%nat).

Example test_derivative : derivative_spec [-5; 0; 0; 0; -4; 0; 0; 0; 1; 1; -5] [0; 0; 0; -16; 0; 0; 0; 8; 9; -50].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.