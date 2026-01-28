Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [2; 0; 3; 0; 3; 0; 2; 0; 1], output = [0; 6; 0; 12; 0; 12; 0; 8] *)
Example test_derivative : derivative_spec [2; 0; 3; 0; 3; 0; 2; 0; 1] [0; 6; 0; 12; 0; 12; 0; 8].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.