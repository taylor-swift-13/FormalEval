Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 2 2 0 2.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 2 -> 2 = 2 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 2 -> 2 = 0 *)
    intros H_not_prime.
    (* We prove that 2 is prime to establish a contradiction *)
    assert (H_is_prime_2 : is_prime 2).
    {
      unfold is_prime.
      split.
      - (* 2 >= 2 *)
        lia.
      - (* Forall d ... *)
        intros d H_ge_2 H_sq.
        (* Since d >= 2, d * d >= 4. But H_sq says d * d <= 2. Contradiction. *)
        nia.
    }
    (* Derive contradiction between H_not_prime and H_is_prime_2 *)
    contradiction.
Qed.