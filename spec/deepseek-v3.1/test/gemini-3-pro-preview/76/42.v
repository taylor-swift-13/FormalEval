Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 10 81 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Hpow]].
    destruct (Z.le_gt_cases 1 k).
    + assert (81 ^ 1 <= 81 ^ k) by (apply Z.pow_le_mono_r; lia).
      simpl in H.
      lia.
    + assert (k = 0) by lia.
      subst.
      simpl in Hpow.
      discriminate.
Qed.