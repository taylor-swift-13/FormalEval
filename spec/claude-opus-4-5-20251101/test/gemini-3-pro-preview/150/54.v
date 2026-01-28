Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 6 1 100 100.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 6 -> 100 = 1 *)
    intros H_prime.
    (* We prove that 6 is not prime to establish a contradiction *)
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* Instantiate forall with d = 2 *)
    assert (H_mod_2 : 6 mod 2 <> 0).
    {
      apply H_forall.
      - (* 2 <= 2 *)
        lia.
      - (* 2 * 2 <= 6 *)
        lia.
    }
    (* 6 mod 2 is 0, which contradicts H_mod_2 *)
    compute in H_mod_2.
    contradiction.
  - (* Case 2: ~is_prime 6 -> 100 = 100 *)
    intros H_not_prime.
    reflexivity.
Qed.