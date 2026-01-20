Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma thirty_six_not_prime : ~is_prime 36.
Proof.
  unfold is_prime.
  intros [_ H].
  specialize (H 6).
  assert (2 <= 6) as H1 by lia.
  assert (6 * 6 <= 36) as H2 by lia.
  specialize (H H1 H2).
  compute in H.
  apply H.
  reflexivity.
Qed.

Example test_x_or_y : x_or_y_spec 36 456 37 37.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    apply thirty_six_not_prime.
    exact Hprime.
  - intros _. reflexivity.
Qed.