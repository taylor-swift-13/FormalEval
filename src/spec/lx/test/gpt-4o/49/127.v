Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_999984_999984 :
  Spec 999984 999984 903088.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hcalc: (2 ^ 999984) mod 999984 = 903088).
  {
    (* Use a computational approach to avoid timeout issues *)
    vm_compute.
    reflexivity.
  }
  rewrite Hcalc.
  reflexivity.
Qed.