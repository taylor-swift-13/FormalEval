Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 5 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Hpow]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H | [H | H]] by lia.
    + subst. simpl in Hpow. discriminate.
    + subst. simpl in Hpow. discriminate.
    + assert (4 ^ 2 <= 4 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H0. lia.
Qed.