Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_spec_test : modp_spec 3%Z 5%Z 3%Z.
Proof.
  unfold modp_spec.
  intros _.
  vm_compute.
  reflexivity.
Qed.