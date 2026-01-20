Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example : modp_spec 9 1000001 512.
Proof.
  unfold modp_spec.
  intro H.
  simpl.
  compute.
  reflexivity.
Qed.