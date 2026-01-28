Require Import List.
Require Import ZArith.
Require Import Nat.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [9; -25; 0; -40; 0; 10; -40; -2; 5; 10] [-25; 0; -120; 0; 50; -240; -14; 40; 90].
Proof.
  unfold derivative_spec.
  reflexivity.
Qed.