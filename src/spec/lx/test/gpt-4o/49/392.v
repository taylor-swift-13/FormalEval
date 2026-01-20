Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_234_9878 :
  Spec 234 9878 126.
Proof.
  unfold Spec.
  intros [Hn Hp].
  simpl.
  reflexivity.
Qed.