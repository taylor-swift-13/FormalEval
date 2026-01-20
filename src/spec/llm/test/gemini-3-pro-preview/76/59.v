Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 8 64 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ 1 <= k) by lia.
    destruct H as [Hz|Hpos].
    + subst. simpl in Heq. discriminate.
    + assert (64 ^ 1 <= 64 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H. lia.
Qed.