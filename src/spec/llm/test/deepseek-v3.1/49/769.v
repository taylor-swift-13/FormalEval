Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example : modp_spec 1011 99997 46121.
Proof.
  unfold modp_spec.
  intro H.
  simpl.
  compute.
  reflexivity.
Qed.