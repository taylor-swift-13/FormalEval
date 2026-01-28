Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 3 33 5212 33.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 3 -> 33 = 33 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 3 -> 33 = 5212 *)
    intros H_not_prime.
    (* We prove that 3 is prime to establish a contradiction *)
    assert (H_is_prime_3 : is_prime 3).
    {
      unfold is_prime.
      split.
      - (* 3 >= 2 *)
        lia.
      - (* Forall d ... *)
        intros d H_ge_2 H_sq.
        (* Since d^2 <= 3 and d >= 2, this is impossible because 2^2 = 4 > 3 *)
        nia.
    }
    (* Derive contradiction between H_not_prime and H_is_prime_3 *)
    contradiction.
Qed.