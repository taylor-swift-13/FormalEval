Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 246 65536 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk1 Hk2]].
    destruct (Z.eq_dec k 0).
    + subst k. simpl in Hk2. lia.
    + assert (k >= 1) by lia.
      assert (Hpow : 65536 ^ 1 <= 65536 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow. lia.
Qed.