Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 5 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k >= 1) as [Hz | Hpos] by lia.
    + subst k. simpl in Hk2. lia.
    + assert (6 ^ 1 <= 6 ^ k) as Hle.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hle.
      lia.
Qed.