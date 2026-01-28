Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 81 25 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H0 | [H1 | H2]] by lia.
    + subst k. simpl in Hk2. lia.
    + subst k. simpl in Hk2. lia.
    + assert (25 ^ 2 <= 25 ^ k) as Hle.
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hk2 in Hle.
      simpl in Hle.
      lia.
Qed.