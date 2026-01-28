Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 81 2188 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - discriminate.
  - intros [k [Hk1 Hk2]].
    assert (Hk : k = 0 \/ k >= 1) by lia.
    destruct Hk as [Hk0 | Hk_ge_1].
    + subst k. simpl in Hk2. discriminate.
    + assert (H : 2188 ^ 1 <= 2188 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      rewrite <- Hk2 in H.
      lia.
Qed.