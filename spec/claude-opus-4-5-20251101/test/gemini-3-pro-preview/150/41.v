Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 500 500 501 501.
Proof.
  unfold x_or_y_spec.
  split.
  - intros H.
    unfold is_prime in H.
    destruct H as [_ H].
    specialize (H 2).
    assert (2 <= 2) by lia.
    assert (2 * 2 <= 500) by lia.
    specialize (H H0 H1).
    compute in H.
    contradiction.
  - intros _.
    reflexivity.
Qed.