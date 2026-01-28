Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_6_78: modp_spec 6 78 64.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 78 > 0 *)
    lia.
  - (* Prove 64 = (2 ^ 6) mod 78 *)
    (* Coq simplifies 2^6 to 64, and 64 mod 78 to 64 automatically *)
    reflexivity.
Qed.