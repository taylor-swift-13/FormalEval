Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 49 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (H_split: k < 4 \/ k >= 4) by lia.
    destruct H_split as [H_lt | H_ge].
    + assert (H_small: k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct H_small as [? | [? | [? | ?]]]; subst; simpl in Hk2; lia.
    + assert (H_mono: 3 ^ 4 <= 3 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      rewrite <- Hk2 in H_mono.
      lia.
Qed.