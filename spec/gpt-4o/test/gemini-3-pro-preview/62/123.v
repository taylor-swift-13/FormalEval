Require Import List.
Require Import ZArith.
Import ListNotations.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  result = map (fun i => (nth i xs 0%Z) * (Z.of_nat i))%Z (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [10; -25; -1; 63; -40; 0; 10; -3; 5]%Z [-25; -2; 189; -160; 0; 60; -21; 40]%Z.
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.