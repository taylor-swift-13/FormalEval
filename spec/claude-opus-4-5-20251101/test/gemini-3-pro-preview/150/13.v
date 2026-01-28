Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 11 1 0 1.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 11 -> 1 = 1 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 11 -> 1 = 0 *)
    intros H_not_prime.
    assert (H_is_prime_11 : is_prime 11).
    {
      unfold is_prime.
      split.
      - lia.
      - intros d H_ge_2 H_sq.
        (* Since d^2 <= 11 and d >= 2, d can be 2 or 3. *)
        assert (d = 2 \/ d = 3) by nia.
        destruct H as [H2 | H3]; subst d; compute; discriminate.
    }
    contradiction.
Qed.