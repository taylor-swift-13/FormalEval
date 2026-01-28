Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [0; 1; 0; 4], output = [1; 0; 12] *)
Example test_derivative : derivative_spec [0; 1; 0; 4] [1; 0; 12].
Proof.
  (* Unfold the specification to see the equality constraint *)
  unfold derivative_spec.

  (* Simplify the expression. 
     1. length [0; 1; 0; 4] reduces to 4.
     2. seq 1 (4 - 1) reduces to [1; 2; 3].
     3. map computes:
        - i=1: nth 1 xs 0 * 1 = 1 * 1 = 1
        - i=2: nth 2 xs 0 * 2 = 0 * 2 = 0
        - i=3: nth 3 xs 0 * 3 = 4 * 3 = 12
  *)
  simpl.

  (* Verify that the computed list equals the expected result *)
  reflexivity.
Qed.