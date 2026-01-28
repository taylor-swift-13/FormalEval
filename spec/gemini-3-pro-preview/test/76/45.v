Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 21 35 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k >= 1) as Hcases by lia.
    destruct Hcases as [Hzero | Hpos].
    + subst k. simpl in Hk2. lia.
    + assert (35 ^ 1 <= 35 ^ k) as Hmono.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hmono.
      lia.
Qed.