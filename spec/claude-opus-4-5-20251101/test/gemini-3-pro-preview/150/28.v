Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 123 499 500 500.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 123 -> 500 = 499 *)
    intros H_prime.
    (* We prove that 123 is not prime because it is divisible by 3 *)
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* Instantiate the forall condition with d = 3 *)
    specialize (H_forall 3).
    (* Verify preconditions for d = 3 *)
    assert (H_bounds : 2 <= 3 /\ 3 * 3 <= 123).
    { lia. }
    destruct H_bounds as [H_ge H_sq].
    specialize (H_forall H_ge H_sq).
    (* Compute 123 mod 3 to show contradiction *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 123 -> 500 = 500 *)
    intros _.
    reflexivity.
Qed.