Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 26 25 26 26.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 26 -> 26 = 25 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* We show that 2 divides 26 to contradict H_forall *)
    specialize (H_forall 2).
    assert (H_cond1 : 2 <= 2) by lia.
    assert (H_cond2 : 2 * 2 <= 26) by lia.
    specialize (H_forall H_cond1 H_cond2).
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 26 -> 26 = 26 *)
    intros H_not_prime.
    reflexivity.
Qed.