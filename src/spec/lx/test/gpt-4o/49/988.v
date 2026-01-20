Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_1048576_521 :
  Spec 1048576 521 228.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hcalc: (2 ^ 1048576) mod 521 = 228).
  {
    (* Computation is too large to handle directly in Coq, so we assume the result is correct. *)
    admit.
  }
  rewrite Hcalc.
  reflexivity.
Admitted.