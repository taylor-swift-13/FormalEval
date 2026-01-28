Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 83 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge Hpow]].
    assert (H_cases: k < 0 \/ k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k >= 4) by lia.
    destruct H_cases as [H_neg | [H0 | [H1 | [H2 | [H3 | H_ge_4]]]]]; subst.
    + lia.
    + simpl in Hpow. discriminate.
    + simpl in Hpow. discriminate.
    + simpl in Hpow. discriminate.
    + simpl in Hpow. discriminate.
    + assert (4 ^ 4 <= 4 ^ k)%Z.
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      lia.
Qed.