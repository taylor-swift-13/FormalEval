Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 1099511627776 2187 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k < 4 \/ k >= 4) as [Hsmall|Hlarge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [->|[->|[->|->]]] by lia;
      vm_compute in Heq; discriminate.
    + assert (H : 2187 ^ 4 <= 2187 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Heq in H.
      vm_compute in H.
      lia.
Qed.