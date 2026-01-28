Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 81 7 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Hpow]].
    assert (k < 3 \/ k >= 3) as [Hsmall | Hlarge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2) as [-> | [-> | ->]] by lia;
      simpl in Hpow; lia.
    + assert (Hmono : 7 ^ 3 <= 7 ^ k) by (apply Z.pow_le_mono_r; lia).
      rewrite <- Hpow in Hmono.
      change (7 ^ 3) with 343 in Hmono.
      lia.
Qed.