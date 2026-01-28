Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 100 99 200 200.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 100 -> 200 = 99 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* We show 100 is not prime because 2 divides it *)
    specialize (H_forall 2).
    assert (H_le : 2 <= 2) by lia.
    assert (H_sq : 2 * 2 <= 100) by lia.
    specialize (H_forall H_le H_sq).
    (* H_forall states 100 mod 2 <> 0, but 100 mod 2 is 0 *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 100 -> 200 = 200 *)
    intros _.
    reflexivity.
Qed.