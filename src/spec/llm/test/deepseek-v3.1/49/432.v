Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example : modp_spec 100000 236 20.
Proof.
  unfold modp_spec.
  intro H.  (* p > 1 *)
  simpl.
  compute.
  reflexivity.
Qed.