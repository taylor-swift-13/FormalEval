Require Import List.
Require Import Nat.
Import ListNotations.

Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

Example test_derivative : derivative_spec [1; 2; 3] [2; 6].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.