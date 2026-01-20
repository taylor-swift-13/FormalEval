Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition x_or_y_spec (n : Z) (x : Z) (y : Z) (result : Z) : Prop :=
  (is_prime n -> result = x) /\ (~is_prime n -> result = y).

Example test_case_1 : x_or_y_spec 7 34 12 34.
Proof.
  unfold x_or_y_spec.
  split.
  - (* Case: is_prime 7 -> 34 = 34 *)
    intros _. 
    reflexivity.
  - (* Case: ~is_prime 7 -> 34 = 12 *)
    intros H_not_prime.
    exfalso. 
    apply H_not_prime.
    unfold is_prime.
    split.
    + (* Prove 7 >= 2 *)
      lia.
    + (* Prove no divisors <= sqrt(7) *)
      intros d H_ge_2 H_sq.
      (* Since d >= 2 and d * d <= 7, d must be 2.
         If d >= 3, then d * d >= 9, which contradicts d * d <= 7. *)
      assert (d = 2) by nia.
      subst d.
      (* Prove 7 mod 2 <> 0 *)
      compute. 
      discriminate.
Qed.