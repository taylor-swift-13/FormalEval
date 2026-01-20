Require Import List.
Require Import Nat.
Import ListNotations.

Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

Example derivative_test : derivative_spec [3; 1; 2; 4; 5] [1; 4; 12; 20].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.