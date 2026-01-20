Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma sixty_two_not_prime : ~is_prime 62.
Proof.
  unfold is_prime.
  intros [Hge2 Hdiv].
  assert (H: 62 mod 2 <> 0).
  { apply Hdiv; lia. }
  compute in H.
  apply H.
  reflexivity.
Qed.

Example test_x_or_y : x_or_y_spec 62 40 62 62.
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    apply sixty_two_not_prime.
    exact Hprime.
  - intros _. reflexivity.
Qed.