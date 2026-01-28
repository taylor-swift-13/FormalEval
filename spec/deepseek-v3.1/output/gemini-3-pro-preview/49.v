Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

Example test_modp : modp_spec 3 5 3.
Proof.
  unfold modp_spec.
  intros H.
  (* Compute 2^3 = 8, and 8 mod 5 = 3 *)
  reflexivity.
Qed.