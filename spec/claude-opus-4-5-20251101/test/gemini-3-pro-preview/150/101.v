Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 62 40 41 41.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 62 -> 41 = 40 *)
    intros H_prime.
    (* 62 is not prime, so H_prime leads to a contradiction *)
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* We show that 2 divides 62 *)
    specialize (H_forall 2).
    assert (H_ge_2: 2 <= 2) by lia.
    assert (H_sq: 2 * 2 <= 62) by lia.
    specialize (H_forall H_ge_2 H_sq).
    (* 62 mod 2 is 0, contradicting H_forall which says it shouldn't be 0 *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 62 -> 41 = 41 *)
    intros _.
    reflexivity.
Qed.