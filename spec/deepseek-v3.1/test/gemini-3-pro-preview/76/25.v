Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 21 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Hpow]].
    assert (k <= 4 \/ k >= 5) by lia.
    destruct H as [Hle | Hge].
    + assert (2 ^ k <= 2 ^ 4). { apply Z.pow_le_mono_r; lia. }
      simpl in H. rewrite Hpow in H. lia.
    + assert (2 ^ 5 <= 2 ^ k). { apply Z.pow_le_mono_r; lia. }
      simpl in H. rewrite Hpow in H. lia.
Qed.