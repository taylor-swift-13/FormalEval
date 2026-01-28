Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 40 0 98 98.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 40 -> 98 = 0 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    specialize (H_forall 2).
    assert (H_bound1: 2 <= 2) by lia.
    assert (H_bound2: 2 * 2 <= 40) by lia.
    specialize (H_forall H_bound1 H_bound2).
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 40 -> 98 = 98 *)
    intros H_not_prime.
    reflexivity.
Qed.