Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 3609 1245 583 583.
Proof.
  unfold x_or_y_spec.
  split.
  - intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    specialize (H_forall 3).
    assert (2 <= 3) by lia.
    assert (3 * 3 <= 3609) by lia.
    specialize (H_forall H H0).
    compute in H_forall.
    destruct H_forall.
    reflexivity.
  - intros H_not_prime.
    reflexivity.
Qed.