Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 2 81 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ 0 < k) as [Hk0 | Hk_pos] by lia.
    + subst k. simpl in Hk2. discriminate.
    + assert (81 <= 81 ^ k).
      {
        replace 81 with (81 ^ 1) at 1 by reflexivity.
        apply Z.pow_le_mono_r; lia.
      }
      lia.
Qed.