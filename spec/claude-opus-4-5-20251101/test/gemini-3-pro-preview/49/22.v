Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_3_3: modp_spec 3 3 2.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 3 > 0 *)
    lia.
  - (* Prove 2 = (2 ^ 3) mod 3 *)
    reflexivity.
Qed.