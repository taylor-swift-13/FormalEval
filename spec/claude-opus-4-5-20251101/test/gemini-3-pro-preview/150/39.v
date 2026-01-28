Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 500 501 500 500.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 500 -> 500 = 501 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* 500 is even, so d=2 is a divisor *)
    specialize (H_forall 2).
    assert (H_le : 2 <= 2) by lia.
    assert (H_sq : 2 * 2 <= 500) by lia.
    specialize (H_forall H_le H_sq).
    (* H_forall is now 500 mod 2 <> 0 *)
    (* Compute 500 mod 2 to show it is 0 *)
    compute in H_forall.
    (* Now H_forall is 0 <> 0, which is a contradiction *)
    contradiction.
  - (* Case 2: ~is_prime 500 -> 500 = 500 *)
    intros _.
    reflexivity.
Qed.