Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma ninety_nine_not_prime : ~is_prime 99.
Proof.
  unfold is_prime.
  intros [_ H].
  assert (H3 : 2 <= 3) by lia.
  assert (H9 : 3 * 3 <= 99) by lia.
  specialize (H 3 H3 H9).
  compute in H.
  apply H.
  reflexivity.
Qed.

Example test_x_or_y : x_or_y_spec 99 3 9 9.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    apply ninety_nine_not_prime.
    exact Hprime.
  - intros _. reflexivity.
Qed.