Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_999999_234 :
  Spec 999999 234 8.
Proof.
  unfold Spec.
  intros [Hn Hp].
  assert (Hmod: (2 ^ 999999) mod 234 = 8).
  {
    (* Use computational tactics to resolve the modulo operation efficiently *)
    vm_compute.
    reflexivity.
  }
  rewrite Hmod.
  reflexivity.
Qed.