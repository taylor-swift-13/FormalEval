Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 2187 2189 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ 0 < k) by lia.
    destruct H as [H | H].
    + subst. simpl in Hk2. lia.
    + assert (Hge: 2189 ^ 1 <= 2189 ^ k) by (apply Z.pow_le_mono_r; lia).
      simpl in Hge.
      lia.
Qed.