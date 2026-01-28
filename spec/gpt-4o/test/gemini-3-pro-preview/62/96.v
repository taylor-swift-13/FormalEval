Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [0; 3; 3; 0; 5; 1; 1; 0; 6; 0], output = [3; 6; 0; 20; 5; 6; 0; 48; 0] *)
Example test_derivative : derivative_spec [0; 3; 3; 0; 5; 1; 1; 0; 6; 0] [3; 6; 0; 20; 5; 6; 0; 48; 0].
Proof.
  unfold derivative_spec.
  simpl.
  reflexivity.
Qed.