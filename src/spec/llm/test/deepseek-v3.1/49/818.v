Require Import ZArith.
Require Import Znumtheory.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example modp_example : modp_spec 100021 54322 31478.
Proof.
  unfold modp_spec.
  intro H.
  (* We verify that 2^100021 mod 54322 equals 31478 *)
  compute.
  reflexivity.
Qed.