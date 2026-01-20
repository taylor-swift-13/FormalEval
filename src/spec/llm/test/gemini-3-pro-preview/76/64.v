Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 24 25 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k = 1 \/ k > 1) by lia.
    destruct H as [H | [H | H]].
    + subst. simpl in Heq. discriminate.
    + subst. simpl in Heq. discriminate.
    + assert (25 ^ 1 < 25 ^ k) by (apply Z.pow_lt_mono_r; lia).
      simpl in H0. lia.
Qed.