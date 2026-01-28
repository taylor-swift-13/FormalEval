Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 4722366482869645213696 1099511627777 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Hx]].
    assert (Hbase : 1099511627777 > 0) by (vm_compute; reflexivity).
    destruct (Z_lt_le_dec k 2) as [Hk_lt | Hk_ge].
    + assert (Hcases : k = 0 \/ k = 1) by lia.
      destruct Hcases as [-> | ->].
      * vm_compute in Hx. lia.
      * vm_compute in Hx. lia.
    + assert (Hpow : 1099511627777 ^ 2 <= 1099511627777 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      assert (Hcalc : 4722366482869645213696 < 1099511627777 ^ 2) by (vm_compute; reflexivity).
      rewrite Hx in Hcalc.
      lia.
Qed.