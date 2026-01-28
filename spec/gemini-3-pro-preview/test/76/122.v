Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 243 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_pos Hk_eq]].
    assert (k < 8 \/ k >= 8) as [H_lt | H_ge] by lia.
    + assert (2 ^ k <= 2 ^ 7) as H_le.
      { apply Z.pow_le_mono_r; lia. }
      change (2 ^ 7) with 128 in H_le.
      lia.
    + assert (2 ^ 8 <= 2 ^ k) as H_le.
      { apply Z.pow_le_mono_r; lia. }
      change (2 ^ 8) with 256 in H_le.
      lia.
Qed.