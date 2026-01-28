Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 25 (-25) 25 25.
Proof.
  unfold x_or_y_spec.
  split.
  - intros H_prime.
    exfalso.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    specialize (H_forall 5).
    assert (H_le : 2 <= 5) by lia.
    assert (H_sq : 5 * 5 <= 25) by lia.
    specialize (H_forall H_le H_sq).
    compute in H_forall.
    apply H_forall.
    reflexivity.
  - intros _.
    reflexivity.
Qed.