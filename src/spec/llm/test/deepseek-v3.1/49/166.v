Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example : modp_spec 233 172871 12294.
Proof.
  unfold modp_spec.
  intros H.
  compute.
  reflexivity.
Qed.