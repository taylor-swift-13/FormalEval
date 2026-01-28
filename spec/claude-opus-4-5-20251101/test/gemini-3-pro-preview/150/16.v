Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 113 100 200 100.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 113 -> 100 = 100 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 113 -> 100 = 200 *)
    intros H_not_prime.
    (* We prove that 113 is prime to establish a contradiction *)
    assert (H_is_prime_113 : is_prime 113).
    {
      unfold is_prime.
      split.
      - (* 113 >= 2 *)
        lia.
      - (* Forall d ... *)
        intros d H_ge_2 H_sq.
        (* d*d <= 113 implies d <= 10 *)
        assert (H_bound : d <= 10) by nia.
        (* Enumerate cases for d from 2 to 10 *)
        assert (H_cases : d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10) by lia.
        destruct H_cases as [H_eq | [H_eq | [H_eq | [H_eq | [H_eq | [H_eq | [H_eq | [H_eq | H_eq]]]]]]]]; subst d; compute; discriminate.
    }
    contradiction.
Qed.