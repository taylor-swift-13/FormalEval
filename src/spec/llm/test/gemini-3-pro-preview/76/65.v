Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 64 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (k < 3 \/ k >= 3) as [Hsmall | Hlarge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2) as [K0 | [K1 | K2]] by lia;
        subst k; simpl in Hk_eq; lia.
    + assert (5 ^ 3 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      lia.
Qed.