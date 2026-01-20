Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 243 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Hpow]].
    assert (k < 4 \/ k >= 4) as [Hlt | Hge4] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [-> | [-> | [-> | ->]]] by lia;
      simpl in Hpow; discriminate.
    + assert (H : 6 ^ 4 <= 6 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      change (6 ^ 4) with 1296 in H.
      lia.
Qed.