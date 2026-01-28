Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 48 0 499 499.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 48 -> 499 = 0 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* We prove 48 is not prime by showing 2 divides it, leading to a contradiction *)
    assert (H_contra : 48 mod 2 <> 0).
    { apply H_forall; lia. }
    compute in H_contra.
    contradiction.
  - (* Case 2: ~is_prime 48 -> 499 = 499 *)
    intros _.
    reflexivity.
Qed.