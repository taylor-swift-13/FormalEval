Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 5 27 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k >= 1) as [Hk0 | Hk_ge_1] by lia.
    + subst k. simpl in Hk2. discriminate.
    + assert (27 ^ 1 <= 27 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      change (27 ^ 1) with 27 in H.
      lia.
Qed.