Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_530123_234 :
  Spec 530123 234 176.
Proof.
  unfold Spec.
  intros [Hn Hp].
  replace (2 ^ 530123 mod 234) with 176 by (vm_compute; reflexivity).
  reflexivity.
Qed.