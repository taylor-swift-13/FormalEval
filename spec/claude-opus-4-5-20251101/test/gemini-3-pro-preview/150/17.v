Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec 17 5 9 5.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime 17 -> 5 = 5 *)
    intros H_prime.
    reflexivity.
  - (* Case 2: ~is_prime 17 -> 5 = 9 *)
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
        (* Since d^2 <= 17 and d >= 2, d can be 2, 3, or 4. *)
        assert (d = 2 \/ d = 3 \/ d = 4) by nia.
        destruct H as [H2 | [H3 | H4]]; subst d; compute; intro H_contra; discriminate H_contra.
    }
    (* Derive contradiction between H_not_prime and H_is_prime_17 *)
    contradiction.
Qed.