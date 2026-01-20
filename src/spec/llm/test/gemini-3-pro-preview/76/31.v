Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 2 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k >= 1) as [Hk0 | Hk1] by lia.
    + subst k. simpl in Heq. discriminate.
    + assert (5 ^ 1 <= 5 ^ k) as Hle.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hle.
      rewrite <- Heq in Hle.
      lia.
Qed.