Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_7_20: modp_spec 7 20 8.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 20 > 0 *)
    lia.
  - (* Prove 8 = (2 ^ 7) mod 20 *)
    (* Coq simplifies 2^7 to 128, and 128 mod 20 to 8 automatically *)
    reflexivity.
Qed.