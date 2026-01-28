Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 25 (-26) 25 25.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 25 -> 25 = -26 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    specialize (H_forall 5).
    assert (H_cond : 2 <= 5 /\ 5 * 5 <= 25) by lia.
    destruct H_cond as [H_ge H_sq].
    specialize (H_forall H_ge H_sq).
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 25 -> 25 = 25 *)
    intros H_not_prime.
    reflexivity.
Qed.