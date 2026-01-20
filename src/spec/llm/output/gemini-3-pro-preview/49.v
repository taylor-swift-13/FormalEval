Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example test_modp : modp_spec 3 5 3.
Proof.
  unfold modp_spec.
  (* 3 = (2 ^ 3) mod 5 *)
  (* 3 = 8 mod 5 *)
  (* 3 = 3 *)
  reflexivity.
Qed.