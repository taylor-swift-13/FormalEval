Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 64 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k < 3 \/ k >= 3) as [Hlt | Hge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2) as [? | [? | ?]] by lia;
      subst k; simpl in Heq; discriminate.
    + assert (6 ^ 3 <= 6 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Heq in Hpow.
      change (6 ^ 3) with 216 in Hpow.
      lia.
Qed.