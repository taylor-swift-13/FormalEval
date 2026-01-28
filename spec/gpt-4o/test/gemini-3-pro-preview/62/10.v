Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [0; 0; 0; 0; 0], output = [0; 0; 0; 0] *)
Example test_derivative : derivative_spec [0; 0; 0; 0; 0] [0; 0; 0; 0].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.