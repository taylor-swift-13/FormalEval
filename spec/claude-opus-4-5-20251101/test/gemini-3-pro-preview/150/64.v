Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 99 (-25) 99 99.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 99 -> 99 = -25 *)
    intros H_prime.
    assert (H_not_prime : ~ is_prime 99).
    {
      unfold is_prime.
      intros [H_ge_2 H_forall].
      (* 3 divides 99, so 99 is not prime *)
      specialize (H_forall 3).
      assert (2 <= 3) by lia.
      assert (3 * 3 <= 99) by lia.
      specialize (H_forall H H0).
      compute in H_forall.
      contradiction.
    }
    contradiction.
  - (* Case 2: ~is_prime 99 -> 99 = 99 *)
    intros H_not_prime.
    reflexivity.
Qed.