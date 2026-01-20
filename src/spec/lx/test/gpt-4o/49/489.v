Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_999983_172871 :
  Spec 999983 172871 141567.
Proof.
  unfold Spec.
  intros [Hn Hp].
  vm_compute.
  reflexivity.
Qed.