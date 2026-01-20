Require Import ZArith.
Open Scope Z_scope.

Definition Spec (n p output : Z) : Prop :=
  (n >= 0 /\ p > 0) -> output = (2 ^ n) mod p.

Example modp_test_999999_19 :
  Spec 999999 19 18.
Proof.
  unfold Spec.
  intros [Hn Hp].
  replace (2 ^ 999999 mod 19) with 18.
  reflexivity.
  (* Precompute the modular exponentiation to avoid timeout *)
  vm_compute.
  reflexivity.
Qed.