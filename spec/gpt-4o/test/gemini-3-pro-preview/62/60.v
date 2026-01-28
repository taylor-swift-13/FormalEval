Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [0; 2; 0; 8; 3; 0; 4; 0; 5], output = [2; 0; 24; 12; 0; 24; 0; 40] *)
Example test_derivative : derivative_spec [0; 2; 0; 8; 3; 0; 4; 0; 5] [2; 0; 24; 12; 0; 24; 0; 40].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.