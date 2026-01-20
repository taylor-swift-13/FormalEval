Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example_1 : modp_spec 3 5 3.
Proof.
  unfold modp_spec.
  intros H.
  simpl.
  reflexivity.
Qed.

Example modp_example_2 : modp_spec 10 23 12.
Proof.
  unfold modp_spec.
  intros H.
  simpl.
  reflexivity.
Qed.