Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma five_hundred_not_prime : ~is_prime 500.
Proof.
  unfold is_prime.
  intros [_ H].
  assert (H2 : 2 <= 2) by lia.
  assert (H4 : 2 * 2 <= 500) by lia.
  specialize (H 2 H2 H4).
  compute in H.
  congruence.
Qed.

Example test_x_or_y : x_or_y_spec 500 500 22 22.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    apply five_hundred_not_prime.
    exact Hprime.
  - intros _. reflexivity.
Qed.