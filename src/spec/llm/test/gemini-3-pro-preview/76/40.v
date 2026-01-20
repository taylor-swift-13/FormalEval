Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 7 15 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k >= 1) by lia.
    destruct H as [Hz | Hp].
    + subst. simpl in Heq. lia.
    + assert (15 ^ 1 <= 15 ^ k) by (apply Z.pow_le_mono_r; lia).
      simpl in H.
      lia.
Qed.