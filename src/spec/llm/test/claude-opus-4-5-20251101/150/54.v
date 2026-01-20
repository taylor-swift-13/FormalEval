Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma six_not_prime : ~is_prime 6.
Proof.
  unfold is_prime.
  intros [Hge2 Hdiv].
  specialize (Hdiv 2).
  assert (2 <= 2) as H1 by lia.
  assert (2 * 2 <= 6) as H2 by lia.
  specialize (Hdiv H1 H2).
  compute in Hdiv.
  apply Hdiv.
  reflexivity.
Qed.

Example test_x_or_y : x_or_y_spec 6 1 100 100.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    apply six_not_prime.
    exact Hprime.
  - intros _. reflexivity.
Qed.