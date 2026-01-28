Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 25 27 25 25.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 25 -> 25 = 27 *)
    intros H_prime.
    (* We prove that 25 is not prime to establish a contradiction *)
    assert (H_not_prime : ~ is_prime 25).
    {
      unfold is_prime.
      intros [_ H_forall].
      (* We provide d = 5 as a counterexample *)
      specialize (H_forall 5).
      assert (2 <= 5) by lia.
      assert (5 * 5 <= 25) by lia.
      specialize (H_forall H H0).
      (* 25 mod 5 is 0, so H_forall becomes 0 <> 0 *)
      compute in H_forall.
      lia.
    }
    contradiction.
  - (* Case 2: ~is_prime 25 -> 25 = 25 *)
    intros H_not_prime.
    reflexivity.
Qed.