Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_5_17 :
  Spec 5 17 15.
Proof.
  unfold Spec.
  intros [Hn Hp].
  simpl.
  reflexivity.
Qed.