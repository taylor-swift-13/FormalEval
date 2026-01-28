Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 41 3 (-26) 3.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 41 -> 3 = 3 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 41 -> 3 = -26 *)
    intros H_not_prime.
    (* We prove that 41 is prime to establish a contradiction *)
    assert (H_is_prime : is_prime 41).
    {
      unfold is_prime.
      split.
      - (* 41 >= 2 *)
        lia.
      - (* Forall d ... *)
        intros d H_ge_2 H_sq.
        (* Since d^2 <= 41 and d >= 2, d <= 6 *)
        assert (d <= 6).
        { nia. }
        (* Enumerate cases for d *)
        assert (H_cases : d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
        destruct H_cases as [H_eq | [H_eq | [H_eq | [H_eq | H_eq]]]]; subst d; compute; discriminate.
    }
    contradiction.
Qed.