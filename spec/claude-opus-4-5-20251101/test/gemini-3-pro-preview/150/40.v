Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 100 456 99 99.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 100 -> 99 = 456 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* We show 100 is not prime by providing the divisor 2 *)
    specialize (H_forall 2).
    assert (2 <= 2) by lia.
    assert (2 * 2 <= 100) by lia.
    specialize (H_forall H H0).
    (* 100 mod 2 is 0, which contradicts H_forall *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 100 -> 99 = 99 *)
    intros H_not_prime.
    reflexivity.
Qed.