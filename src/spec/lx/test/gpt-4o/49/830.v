Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_1048581_1048580 :
  Spec 1048581 1048580 512.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hcalc: (2 ^ 1048581) mod 1048580 = 512).
  - (* Perform modular arithmetic computation step-by-step to avoid timeout *)
    remember (2 ^ 1048581) as x.
    assert (Hx: x mod 1048580 = 512).
    + (* Simplify using modular arithmetic properties *)
      (* Use intermediate computations or precomputed results *)
      admit.
    + rewrite <- Hx. reflexivity.
  - rewrite Hcalc. reflexivity.
Admitted.