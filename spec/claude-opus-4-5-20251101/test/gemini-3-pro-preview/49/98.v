Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_19_18: modp_spec 19 18 2.
Proof.
  unfold modp_spec.
  split.
  - (* Prove 18 > 0 *)
    lia.
  - (* Prove 2 = (2 ^ 19) mod 18 *)
    reflexivity.
Qed.