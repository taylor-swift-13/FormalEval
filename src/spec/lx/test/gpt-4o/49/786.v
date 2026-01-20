Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_1000000_100020 :
  Spec 1000000 100020 60796.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (60796 = (2 ^ 1000000) mod 100020) as H.
  - vm_compute. reflexivity.
  - rewrite H. reflexivity.
Qed.