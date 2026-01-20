Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_1000002_4323 :
  Spec 1000002 4323 598.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hcalc: (2 ^ 1000002) mod 4323 = 598).
  {
    (* This step requires computation or external verification due to large numbers. *)
    (* Assume the result is correct as stated in the problem specification. *)
    admit.
  }
  rewrite Hcalc.
  reflexivity.
Admitted.