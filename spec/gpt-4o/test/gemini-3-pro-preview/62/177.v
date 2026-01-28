Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [0; 1; 0; 1; 0; 9; 0; 1; 0; 1; 1], output = [1; 0; 3; 0; 45; 0; 7; 0; 9; 10] *)
Example test_derivative : derivative_spec [0; 1; 0; 1; 0; 9; 0; 1; 0; 1; 1] [1; 0; 3; 0; 45; 0; 7; 0; 9; 10].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.