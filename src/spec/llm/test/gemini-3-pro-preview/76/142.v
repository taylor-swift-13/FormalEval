Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 2188 16777216 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Heq]].
    destruct (Z.eq_dec k 0).
    + subst. simpl in Heq. lia.
    + assert (Hk1 : k >= 1) by lia.
      assert (Hpow : 16777216 ^ 1 <= 16777216 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      lia.
Qed.