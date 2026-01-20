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
  intros [Hge2 Hdiv].
  assert (H: 500 mod 2 <> 0).
  { apply Hdiv; lia. }
  compute in H.
  congruence.
Qed.

Example test_x_or_y : x_or_y_spec 500 500 500 500.
Proof.
  unfold x_or_y_spec.
  split.
  - intros _. reflexivity.
  - intros _. reflexivity.
Qed.