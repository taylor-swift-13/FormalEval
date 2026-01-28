Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 501 456 37 37.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 501 -> 37 = 456 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* 501 is divisible by 3, so it is not prime *)
    specialize (H_forall 3).
    assert (H_bounds : 2 <= 3 /\ 3 * 3 <= 501) by lia.
    destruct H_bounds as [H_ge H_sq].
    specialize (H_forall H_ge H_sq).
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 501 -> 37 = 37 *)
    intros H_not_prime.
    reflexivity.
Qed.