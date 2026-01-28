Require Import List.
Require Import Nat.
Import ListNotations.

Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [4; 0; 1; 8; 0; 4; 0; 0] [0; 2; 24; 0; 20; 0; 0].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.