Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 6 123 100 100.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 6 -> 100 = 123 *)
    intros H_prime.
    (* 6 is not prime, so H_prime is false. We derive a contradiction. *)
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* Instantiate forall with d = 2 *)
    specialize (H_forall 2).
    assert (H_cond1 : 2 <= 2) by lia.
    assert (H_cond2 : 2 * 2 <= 6) by lia.
    specialize (H_forall H_cond1 H_cond2).
    (* 6 mod 2 computes to 0 *)
    compute in H_forall.
    (* H_forall is now 0 <> 0, which is a contradiction *)
    contradiction.
  - (* Case 2: ~is_prime 6 -> 100 = 100 *)
    intros _.
    reflexivity.
Qed.