Require Import List.
Require Import Nat.
Import ListNotations.

Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [0; 0; 0; 6; 0; 0; 0; 0; 1; 7; 0; 0; 0; 8] [0; 0; 18; 0; 0; 0; 0; 8; 63; 0; 0; 0; 104].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.