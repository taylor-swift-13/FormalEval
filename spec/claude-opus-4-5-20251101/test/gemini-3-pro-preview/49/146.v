Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_1000003_1000003: modp_spec 1000003 1000003 2.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - vm_compute. reflexivity.
Qed.