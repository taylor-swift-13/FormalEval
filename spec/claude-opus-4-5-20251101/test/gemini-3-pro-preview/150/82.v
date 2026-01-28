Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 37 123 6 123.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 37 -> 123 = 123 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 37 -> 123 = 6 *)
    intros H_not_prime.
    (* We prove that 37 is prime to establish a contradiction *)
    assert (H_is_prime_37 : is_prime 37).
    {
      unfold is_prime.
      split.
      - lia.
      - intros d H_ge_2 H_sq.
        (* Since d^2 <= 37, d must be < 7 *)
        assert (d < 7) by nia.
        (* Enumerate possible values for d *)
        assert (H_cases: d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
        (* Check each case *)
        destruct H_cases as [H_eq | [H_eq | [H_eq | [H_eq | H_eq]]]]; subst d; compute; intro H_contra; discriminate H_contra.
    }
    contradiction.
Qed.