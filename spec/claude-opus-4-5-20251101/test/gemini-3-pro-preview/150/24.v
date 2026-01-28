Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 5 100 5 100.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 5 -> 100 = 100 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 5 -> 100 = 5 *)
    intros H_not_prime.
    (* We prove that 5 is prime to establish a contradiction *)
    assert (H_is_prime_5 : is_prime 5).
    {
      unfold is_prime.
      split.
      - (* 5 >= 2 *)
        lia.
      - (* Forall d ... *)
        intros d H_ge_2 H_sq.
        (* Since d^2 <= 5 and d >= 2, d must be 2. *)
        (* If d >= 3, then d^2 >= 9, which contradicts H_sq. *)
        assert (d < 3).
        {
          nia.
        }
        (* Therefore d = 2 *)
        assert (d = 2) by lia.
        subst d.
        (* Check 5 mod 2 <> 0. 5 mod 2 computes to 1. *)
        compute.
        intro H_contra.
        discriminate H_contra.
    }
    (* Derive contradiction between H_not_prime and H_is_prime_5 *)
    contradiction.
Qed.