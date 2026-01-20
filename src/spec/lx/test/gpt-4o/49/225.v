Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_530122_231 :
  Spec 530122 231 37.
Proof.
  unfold Spec.
  intros [Hn Hp].
  compute.
  reflexivity.
Qed.