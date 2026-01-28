Require Import List ZArith PeanoNat.
Import ListNotations.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Fixpoint sum_to_n (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => n + sum_to_n n'
  end.

Definition f_spec (n : nat) (result : list nat) : Prop :=
  result = map (fun i => if Nat.even i then factorial i else sum_to_n i) (seq 1 n).

Example test_case_proof : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  (* Unfold the specification definition to expose the equality *)
  unfold f_spec.
  
  (* Simplify the expression:
     1. expands (seq 1 5) to [1; 2; 3; 4; 5]
     2. evaluates the map function
     3. computes Nat.even, factorial, and sum_to_n for the concrete values
  *)
  simpl.
  
  (* Verify that the computed list [1; 2; 6; 24; 15] equals the expected list *)
  reflexivity.
Qed.