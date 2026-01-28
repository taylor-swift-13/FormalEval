Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_7_7: modp_spec 7 7 2.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 7 > 0 *)
    lia.
  - (* Prove 2 = (2 ^ 7) mod 7 *)
    (* Coq simplifies 2^7 to 128, and 128 mod 7 to 2 automatically *)
    reflexivity.
Qed.