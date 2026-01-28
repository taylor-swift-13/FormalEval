Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 500 500 22 22.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 500 -> 22 = 500 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* 500 is divisible by 2, so it is not prime *)
    specialize (H_forall 2).
    assert (H_bounds: 2 <= 2 /\ 2 * 2 <= 500) by lia.
    destruct H_bounds as [H_le H_sq].
    specialize (H_forall H_le H_sq).
    (* 500 mod 2 = 0, contradiction with H_forall which expects <> 0 *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 500 -> 22 = 22 *)
    intros H_not_prime.
    reflexivity.
Qed.