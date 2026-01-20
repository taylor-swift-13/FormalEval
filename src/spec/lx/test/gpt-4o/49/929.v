Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_47_47 :
  Spec 47 47 2.
Proof.
  unfold Spec.
  intros [Hn Hp].
  simpl.
  reflexivity.
Qed.