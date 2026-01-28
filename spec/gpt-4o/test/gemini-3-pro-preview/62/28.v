Require Import List.
Require Import Nat.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition derivative_spec (xs : list nat) (result : list nat) : Prop :=
  result = map (fun i => nth i xs 0 * i) (seq 1 (length xs - 1)).

(* Test case: input = [0; 0; 0; 0; 0; 0; 5], output = [0; 0; 0; 0; 0; 30] *)
Example test_derivative : derivative_spec [0; 0; 0; 0; 0; 0; 5] [0; 0; 0; 0; 0; 30].
Proof.
  (* Unfold the specification to see the equality constraint *)
  unfold derivative_spec.

  (* Simplify the expression. 
     1. length [0; 0; 0; 0; 0; 0; 5] reduces to 7.
     2. seq 1 (7 - 1) reduces to [1; 2; 3; 4; 5; 6].
     3. map computes the derivative terms:
        - i=1..5: nth i xs 0 is 0, so result is 0.
        - i=6: nth 6 xs 0 is 5, so result is 5 * 6 = 30.
  *)
  simpl.

  (* Verify that the computed list equals the expected result *)
  reflexivity.
Qed.