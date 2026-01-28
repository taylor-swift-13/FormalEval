Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 3 65536 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk Hx]].
    assert (k = 0 \/ k > 0) as [Hk0 | Hk_pos] by lia.
    + subst k.
      simpl in Hx.
      discriminate Hx.
    + assert (65536 ^ 1 <= 65536 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hx in Hpow.
      simpl in Hpow.
      lia.
Qed.