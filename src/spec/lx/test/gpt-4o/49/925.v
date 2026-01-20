Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_999981_999981 :
  Spec 999981 999981 512.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hmod: (2 ^ 999981) mod 999981 = 512).
  {
    (* Use a computational approach to directly verify the modulo operation *)
    vm_compute.
    reflexivity.
  }
  rewrite Hmod.
  reflexivity.
Qed.