Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma four_hundred_ninety_eight_not_prime : ~is_prime 498.
Proof.
  unfold is_prime.
  intros [Hge H].
  specialize (H 2).
  assert (2 <= 2) as H1 by lia.
  assert (2 * 2 <= 498) as H2 by lia.
  specialize (H H1 H2).
  compute in H.
  apply H.
  reflexivity.
Qed.

Example test_x_or_y : x_or_y_spec 498 501 500 500.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    apply four_hundred_ninety_eight_not_prime.
    exact Hprime.
  - intros _. reflexivity.
Qed.