Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example : modp_spec 88 89 1.
Proof.
  unfold modp_spec.
  intro H.  (* Assume p > 1 *)
  simpl.
  compute.
  reflexivity.
Qed.