Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 24 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Hpow]].
    destruct (Z_lt_le_dec k 5).
    + assert (Hle: 2 ^ k <= 2 ^ 4).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hle.
      rewrite <- Hpow in Hle.
      lia.
    + assert (Hge: 2 ^ 5 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hge.
      rewrite <- Hpow in Hge.
      lia.
Qed.