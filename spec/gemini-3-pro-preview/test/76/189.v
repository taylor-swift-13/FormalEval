Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 246 245 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [-> | [-> | Hge]] by lia.
    + simpl in Heq. discriminate Heq.
    + simpl in Heq. discriminate Heq.
    + assert (Hpow : 245 ^ 2 <= 245 ^ k) by (apply Z.pow_le_mono_r; lia).
      simpl in Hpow. rewrite <- Heq in Hpow. lia.
Qed.