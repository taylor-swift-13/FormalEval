Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 4 24 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k > 0) as [H0 | Hpos] by lia.
    + subst k. simpl in Hk2. discriminate Hk2.
    + assert (24 ^ 1 <= 24 ^ k) by (apply Z.pow_le_mono_r; lia).
      simpl in H.
      lia.
Qed.