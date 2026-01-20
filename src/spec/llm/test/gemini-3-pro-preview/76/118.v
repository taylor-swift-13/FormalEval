Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 2188 2189 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k >= 1) by lia.
    destruct H as [Hk0 | Hk_ge_1].
    + subst. simpl in Hk2. discriminate.
    + assert (2189 ^ 1 <= 2189 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      rewrite <- Hk2 in H.
      lia.
Qed.