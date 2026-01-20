Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma forty_nine_not_prime : ~is_prime 49.
Proof.
  unfold is_prime.
  intros [_ H].
  assert (H7 : 2 <= 7) by lia.
  assert (H49 : 7 * 7 <= 49) by lia.
  specialize (H 7 H7 H49).
  compute in H.
  apply H.
  reflexivity.
Qed.

Example test_x_or_y : x_or_y_spec 49 3 3 3.
Proof.
  unfold x_or_y_spec.
  split.
  - intros _. reflexivity.
  - intros _. reflexivity.
Qed.