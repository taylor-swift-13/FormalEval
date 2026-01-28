Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.Micromega.Lia.
Open Scope Z_scope.

Definition modp_spec (n p result : Z) : Prop :=
  result = (2 ^ n) mod p.

Example test_modp : modp_spec 1000002 1000001 421982.
Proof.
  unfold modp_spec.
  rewrite Zpower_mod; try lia.
  vm_compute.
  reflexivity.
Qed.