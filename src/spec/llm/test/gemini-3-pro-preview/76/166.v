Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 3 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [ -> | [ -> | Hge2 ]] by lia.
    + simpl in Hk2.
      discriminate.
    + simpl in Hk2.
      discriminate.
    + assert (5 ^ 2 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      rewrite <- Hk2 in H.
      lia.
Qed.