Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_999999_100019: modp_spec 999999 100019 54811.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - vm_compute. reflexivity.
Qed.