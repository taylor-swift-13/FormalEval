Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 1000 62 501 501.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 1000 -> 501 = 62 *)
    intros H_prime.
    (* 1000 is not prime, so H_prime is false. We derive a contradiction. *)
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* We show that 2 divides 1000, contradicting the primality condition. *)
    specialize (H_forall 2).
    assert (H_le : 2 <= 2) by lia.
    assert (H_sq : 2 * 2 <= 1000) by lia.
    specialize (H_forall H_le H_sq).
    (* 1000 mod 2 is 0 *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 1000 -> 501 = 501 *)
    intros _.
    reflexivity.
Qed.