Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 50 49 3 3.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 50 -> 3 = 49 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* We prove that 50 is not prime by finding a divisor, d = 2 *)
    specialize (H_forall 2).
    assert (H_bounds : 2 <= 2 /\ 2 * 2 <= 50) by lia.
    destruct H_bounds as [H_ge H_sq].
    specialize (H_forall H_ge H_sq).
    (* 50 mod 2 is 0, so H_forall becomes 0 <> 0 *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 50 -> 3 = 3 *)
    intros H_not_prime.
    reflexivity.
Qed.