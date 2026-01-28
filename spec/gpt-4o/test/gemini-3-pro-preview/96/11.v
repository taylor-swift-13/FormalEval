Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example test_case : count_up_to_spec 2 [].
Proof.
  unfold count_up_to_spec.
  split.
  
  (* Part 1: Prove that all elements in [] are primes < 2 *)
  - intros x H_in.
    inversion H_in.

  (* Part 2: Prove that all primes < 2 are in [] *)
  - intros x H_bound H_prime.
    (* The range 2 <= x < 2 is empty *)
    lia.
Qed.