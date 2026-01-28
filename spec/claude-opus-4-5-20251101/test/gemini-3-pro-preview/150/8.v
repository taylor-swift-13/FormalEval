Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 6 34 1234 1234.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 6 -> 1234 = 34 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* Show that 2 divides 6 to contradict primality *)
    specialize (H_forall 2).
    assert (H_pre : 2 <= 2 /\ 2 * 2 <= 6) by lia.
    specialize (H_forall (proj1 H_pre) (proj2 H_pre)).
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 6 -> 1234 = 1234 *)
    intros H_not_prime.
    reflexivity.
Qed.