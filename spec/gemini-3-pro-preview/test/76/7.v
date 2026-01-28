Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 128 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - discriminate.
  - intros [k [Hpos Heq]].
    assert (k <= 3 \/ k >= 4) by lia.
    destruct H as [Hle | Hge].
    + assert (4 ^ k <= 4 ^ 3).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Heq in H. simpl in H. lia.
    + assert (4 ^ 4 <= 4 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Heq in H. simpl in H. lia.
Qed.