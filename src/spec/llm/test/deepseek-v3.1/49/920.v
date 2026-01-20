Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example : modp_spec 3 5 3.
Proof.
  unfold modp_spec.
  intro H.
  simpl.
  reflexivity.
Qed.

Example modp_new_test : modp_spec 235 530123 200639.
Proof.
  unfold modp_spec.
  intro H.
  replace (2 ^ 235) with (Z.pow 2 235) by reflexivity.
  compute.
  reflexivity.
Qed.