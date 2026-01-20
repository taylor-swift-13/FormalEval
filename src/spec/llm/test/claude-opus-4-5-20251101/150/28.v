Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma one_two_three_not_prime : ~is_prime 123.
Proof.
  unfold is_prime.
  intros [Hge2 Hdiv].
  specialize (Hdiv 3).
  assert (H1: 2 <= 3) by lia.
  assert (H2: 3 * 3 <= 123) by lia.
  specialize (Hdiv H1 H2).
  compute in Hdiv.
  congruence.
Qed.

Example test_x_or_y : x_or_y_spec 123 499 500 500.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    apply one_two_three_not_prime.
    exact Hprime.
  - intros _. reflexivity.
Qed.