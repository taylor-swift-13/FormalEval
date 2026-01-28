Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 399 2 0 0.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 399 -> 0 = 2 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* 399 is divisible by 3, so it is not prime. We use this to derive a contradiction. *)
    specialize (H_forall 3).
    assert (H_ge_2 : 2 <= 3) by lia.
    assert (H_sq : 3 * 3 <= 399) by lia.
    specialize (H_forall H_ge_2 H_sq).
    (* 399 mod 3 evaluates to 0 *)
    compute in H_forall.
    (* H_forall is now 0 <> 0, which is a contradiction *)
    contradiction.
  - (* Case 2: ~is_prime 399 -> 0 = 0 *)
    intros H_not_prime.
    reflexivity.
Qed.