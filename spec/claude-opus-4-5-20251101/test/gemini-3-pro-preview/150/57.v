Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 31 500 22 500.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 31 -> 500 = 500 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 31 -> 500 = 22 *)
    intros H_not_prime.
    (* We prove that 31 is prime to establish a contradiction *)
    assert (H_is_prime : is_prime 31).
    {
      unfold is_prime.
      split.
      - (* 31 >= 2 *)
        lia.
      - (* Forall d ... *)
        intros d H_ge_2 H_sq.
        (* Since d^2 <= 31 and d >= 2, d must be 2, 3, 4, or 5 *)
        assert (H_cases : d = 2 \/ d = 3 \/ d = 4 \/ d = 5) by nia.
        destruct H_cases as [H2 | [H3 | [H4 | H5]]]; subst d; compute; intro H_contra; discriminate H_contra.
    }
    contradiction.
Qed.