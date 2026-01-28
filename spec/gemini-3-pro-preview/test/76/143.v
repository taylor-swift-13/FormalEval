Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 246 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk1 Hk2]].
    assert (H : k < 4 \/ k >= 4) by lia.
    destruct H as [H | H].
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct H0 as [? | [? | [? | ?]]]; subst k; simpl in Hk2; lia.
    + assert (5 ^ 4 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H0.
      lia.
Qed.