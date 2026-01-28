Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 49 0 3 3.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 49 -> 3 = 0 *)
    intros H_prime.
    (* We prove ~is_prime 49 to establish a contradiction *)
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* 49 is divisible by 7, so we instantiate the forall with 7 *)
    specialize (H_forall 7).
    assert (H_bounds : 2 <= 7 /\ 7 * 7 <= 49) by lia.
    destruct H_bounds as [H_ge H_sq].
    specialize (H_forall H_ge H_sq).
    (* Check 49 mod 7 <> 0. 49 mod 7 computes to 0. *)
    compute in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 49 -> 3 = 3 *)
    intros H_not_prime.
    reflexivity.
Qed.