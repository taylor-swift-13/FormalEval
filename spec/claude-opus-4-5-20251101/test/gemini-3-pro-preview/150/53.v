Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 17 18 9 18.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 17 -> 18 = 18 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 17 -> 18 = 9 *)
    intros H_not_prime.
    (* We prove that 17 is prime to establish a contradiction *)
    assert (H_is_prime_17 : is_prime 17).
    {
      unfold is_prime.
      split.
      - (* 17 >= 2 *)
        lia.
      - (* Forall d ... *)
        intros d H_ge_2 H_sq.
        (* Since d^2 <= 17 and d >= 2, d must be 2, 3, or 4. *)
        (* 5^2 = 25 > 17. *)
        assert (H_bound : d < 5) by nia.
        assert (H_cases : d = 2 \/ d = 3 \/ d = 4) by lia.
        destruct H_cases as [Eq2 | [Eq3 | Eq4]].
        + (* d = 2 *)
          subst d.
          compute.
          intro H_contra.
          discriminate H_contra.
        + (* d = 3 *)
          subst d.
          compute.
          intro H_contra.
          discriminate H_contra.
        + (* d = 4 *)
          subst d.
          compute.
          intro H_contra.
          discriminate H_contra.
    }
    (* Derive contradiction between H_not_prime and H_is_prime_17 *)
    contradiction.
Qed.