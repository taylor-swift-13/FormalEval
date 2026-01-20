Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Lemma neg28_not_prime : ~is_prime (-28).
Proof.
  unfold is_prime.
  intros [H _].
  lia.
Qed.

Example test_x_or_y : x_or_y_spec (-28) (-27) (-4) (-4).
Proof.
  unfold x_or_y_spec.
  split.
  - intros Hprime.
    exfalso.
    apply neg28_not_prime.
    exact Hprime.
  - intros _. reflexivity.
Qed.