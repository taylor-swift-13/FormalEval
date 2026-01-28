Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 37 123 25 123.
Proof.
  unfold x_or_y_spec.
  split.
  - intros H_prime.
    reflexivity.
  - intros H_not_prime.
    assert (H_is_prime_37 : is_prime 37).
    {
      unfold is_prime.
      split.
      - lia.
      - intros d H_ge_2 H_sq.
        assert (H_cases : d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6).
        { assert (d < 7) by nia. lia. }
        destruct H_cases as [-> | [-> | [-> | [-> | ->]]]]; compute; discriminate.
    }
    contradiction.
Qed.