Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 16777216 240 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k < 4 \/ k >= 4) by lia.
    destruct H as [Hlt|Hge].
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct H as [?|[?|[?|?]]]; subst; simpl in Hk2; discriminate.
    + assert (Hpow: 240 ^ 4 <= 240 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk2 in Hpow.
      change (240 ^ 4) with 3317760000 in Hpow.
      lia.
Qed.