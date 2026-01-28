Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 100 456 100 100.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 100 -> 100 = 456 *)
    intros H_prime.
    (* 100 is not prime (divisible by 2), so we derive a contradiction *)
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* Instantiate the quantifier with d = 2 *)
    specialize (H_forall 2).
    (* Prove the conditions 2 <= 2 and 2 * 2 <= 100 *)
    assert (H_cond1 : 2 <= 2) by lia.
    assert (H_cond2 : 2 * 2 <= 100) by lia.
    specialize (H_forall H_cond1 H_cond2).
    (* 100 mod 2 is 0, so H_forall becomes 0 <> 0 *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 100 -> 100 = 100 *)
    intros H_not_prime.
    reflexivity.
Qed.