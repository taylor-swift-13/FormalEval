Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case : x_or_y_spec (-3) (-3) 9 9.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case 1: is_prime (-3) -> 9 = -3 *)
    intros H_prime.
    unfold is_prime in H_prime.
    destruct H_prime as [H_ge_2 _].
    (* -3 >= 2 is a contradiction *)
    lia.
  - (* Case 2: ~is_prime (-3) -> 9 = 9 *)
    intros H_not_prime.
    reflexivity.
Qed.