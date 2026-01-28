Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 243 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (H_cases: k <= 3 \/ k >= 4) by lia.
    destruct H_cases as [H_le | H_ge].
    + assert (4 ^ k <= 4 ^ 3) by (apply Z.pow_le_mono_r; lia).
      simpl in *.
      lia.
    + assert (4 ^ 4 <= 4 ^ k) by (apply Z.pow_le_mono_r; lia).
      simpl in *.
      lia.
Qed.