Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 40 61 62 62.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 40 -> 62 = 61 *)
    intros H_prime.
    (* We prove that 40 is not prime to establish a contradiction *)
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* 40 is divisible by 2, which contradicts the primality property *)
    specialize (H_forall 2).
    assert (H_le : 2 <= 2) by lia.
    assert (H_sq : 2 * 2 <= 40) by lia.
    specialize (H_forall H_le H_sq).
    (* 40 mod 2 computes to 0 *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 40 -> 62 = 62 *)
    intros H_not_prime.
    reflexivity.
Qed.