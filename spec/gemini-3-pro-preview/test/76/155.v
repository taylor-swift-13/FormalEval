Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 26 27 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k > 0) as [Hk0 | Hk_pos] by lia.
    + subst k. simpl in Heq. lia.
    + assert (27 ^ 1 <= 27 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      rewrite <- Heq in Hpow.
      lia.
Qed.