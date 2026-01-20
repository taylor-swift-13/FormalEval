Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example : modp_spec 100020 9878 3576.
Proof.
  unfold modp_spec.
  intro H.
  compute.
  reflexivity.
Qed.