Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 91 56 129 129.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 91 -> 129 = 56 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [_ H_forall].
    (* We show 91 is not prime by finding a divisor, 7 *)
    specialize (H_forall 7).
    (* Prove preconditions for the quantifier *)
    assert (2 <= 7) by lia.
    assert (7 * 7 <= 91) by lia.
    specialize (H_forall H H0).
    (* H_forall states 91 mod 7 <> 0 *)
    (* We prove 91 mod 7 = 0 to contradict *)
    assert (91 mod 7 = 0) by reflexivity.
    rewrite H1 in H_forall.
    contradiction.
  - (* Case 2: ~is_prime 91 -> 129 = 129 *)
    intros H_not_prime.
    reflexivity.
Qed.