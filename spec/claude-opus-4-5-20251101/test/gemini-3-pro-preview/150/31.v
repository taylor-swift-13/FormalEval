Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 37 122 455 122.
Proof.
  unfold x_or_y_spec.
  split.
  - intros H.
    reflexivity.
  - intros H.
    assert (H_prime : is_prime 37).
    {
      unfold is_prime.
      split.
      - lia.
      - intros d H_ge_2 H_sq.
        assert (d <= 6) by nia.
        assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as H_cases by lia.
        destruct H_cases as [H2 | [H3 | [H4 | [H5 | H6]]]]; subst d; compute; discriminate.
    }
    contradiction.
Qed.