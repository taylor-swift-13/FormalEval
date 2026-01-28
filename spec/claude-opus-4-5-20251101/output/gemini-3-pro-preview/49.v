Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_3_5: modp_spec 3 5 3.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 5 > 0 *)
    lia.
  - (* Prove 3 = (2 ^ 3) mod 5 *)
    (* Coq simplifies 2^3 to 8, and 8 mod 5 to 3 automatically *)
    reflexivity.
Qed.