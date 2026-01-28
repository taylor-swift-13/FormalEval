Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 243 242 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk0 | [Hk1_eq | Hk2_ge]] by lia.
    + subst k. simpl in Hk2. lia.
    + subst k. simpl in Hk2. lia.
    + assert (Hpow: 242 ^ 2 <= 242 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk2 in Hpow.
      assert (Hval: 242 ^ 2 = 58564) by reflexivity.
      rewrite Hval in Hpow.
      lia.
Qed.