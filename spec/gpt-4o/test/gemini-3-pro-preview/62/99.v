Require Import List.
Require Import Nat.
Import ListNotations.

Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [8; 0; 0; 0; 6; 0; 0; 6; 7; 0; 0; 1; 7; 0; 0; 0; 8; 7; 0; 8] [0; 0; 0; 24; 0; 0; 42; 56; 0; 0; 11; 84; 0; 0; 0; 128; 119; 0; 152].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.