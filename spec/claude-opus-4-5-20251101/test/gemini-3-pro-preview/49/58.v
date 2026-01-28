Require Import ZArith.
Require Import Zdiv.
Require Import Psatz.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp_112_101: modp_spec 112 101 56.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - vm_compute. reflexivity.
Qed.