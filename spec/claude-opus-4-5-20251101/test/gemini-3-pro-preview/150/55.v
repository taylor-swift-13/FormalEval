Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 99 40 99 99.
Proof.
  unfold x_or_y_spec.
  split.
  - intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    specialize (H_forall 3).
    assert (H_check : 2 <= 3 /\ 3 * 3 <= 99) by lia.
    destruct H_check as [H_ge H_sq].
    specialize (H_forall H_ge H_sq).
    compute in H_forall.
    contradiction.
  - intros _.
    reflexivity.
Qed.