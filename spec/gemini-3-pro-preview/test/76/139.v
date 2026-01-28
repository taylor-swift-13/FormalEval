Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 245 2188 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k >= 1) by lia.
    destruct H as [H | H].
    + subst. simpl in Hk2. discriminate.
    + assert (2188 ^ 1 <= 2188 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H0.
      lia.
Qed.