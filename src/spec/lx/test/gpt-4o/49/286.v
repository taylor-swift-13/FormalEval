Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_530124_9875 :
  Spec 530124 9875 3091.
Proof.
  unfold Spec.
  intros [Hn Hp].
  vm_compute.
  reflexivity.
Qed.