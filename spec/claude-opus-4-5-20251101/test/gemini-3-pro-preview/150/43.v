Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 31 1 31 1.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 31 -> 1 = 1 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 31 -> 1 = 31 *)
    intros H_not_prime.
    assert (H_is_prime_31 : is_prime 31).
    {
      unfold is_prime.
      split.
      - lia.
      - intros d H_ge_2 H_sq.
        assert (H_bound : d < 6) by nia.
        assert (H_cases : d = 2 \/ d = 3 \/ d = 4 \/ d = 5) by lia.
        destruct H_cases as [H_eq | [H_eq | [H_eq | H_eq]]]; subst d; compute; discriminate.
    }
    contradiction.
Qed.