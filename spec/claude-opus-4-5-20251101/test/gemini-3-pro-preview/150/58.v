Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 5 101 5 101.
Proof.
  unfold x_or_y_spec.
  split.
  - intros H_prime.
    reflexivity.
  - intros H_not_prime.
    assert (H_is_prime_5 : is_prime 5).
    {
      unfold is_prime.
      split.
      - lia.
      - intros d H_ge_2 H_sq.
        assert (d = 2).
        { nia. }
        subst d.
        compute.
        intro H_contra.
        discriminate H_contra.
    }
    contradiction.
Qed.