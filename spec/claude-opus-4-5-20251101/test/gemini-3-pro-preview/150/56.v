Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 41 0 3 0.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 41 -> 0 = 0 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 41 -> 0 = 3 *)
    intros H_not_prime.
    assert (H_is_prime_41 : is_prime 41).
    {
      unfold is_prime.
      split.
      - (* 41 >= 2 *)
        lia.
      - (* Forall d ... *)
        intros d H_ge_2 H_sq.
        (* d*d <= 41 implies d < 7 *)
        assert (d < 7).
        { nia. }
        (* Enumerate possible values for d *)
        assert (H_cases : d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
        destruct H_cases as [-> | [-> | [-> | [-> | ->]]]]; compute; discriminate.
    }
    contradiction.
Qed.