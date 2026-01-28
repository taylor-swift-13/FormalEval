Require Import List.
Require Import ZArith.
Require Import Nat.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => nth i xs 0 * Z.of_nat i) (seq 1%nat (length xs - 1)%nat).

Example test_derivative : derivative_spec [0; 2; 0; 0; 4; -1; 5] [2; 0; 0; 16; -5; 30].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.