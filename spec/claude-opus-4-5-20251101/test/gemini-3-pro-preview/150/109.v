Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 500 22 500 500.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 500 -> 500 = 22 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* We show 500 is not prime because it is divisible by 2 *)
    specialize (H_forall 2).
    assert (H_cond1 : 2 <= 2) by lia.
    assert (H_cond2 : 2 * 2 <= 500) by lia.
    specialize (H_forall H_cond1 H_cond2).
    (* H_forall reduces to 0 <> 0, which is a contradiction *)
    compute in H_forall.
    destruct H_forall.
    reflexivity.
  - (* Case 2: ~is_prime 500 -> 500 = 500 *)
    intros H_not_prime.
    reflexivity.
Qed.