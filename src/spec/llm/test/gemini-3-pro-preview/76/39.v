Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 15 23 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge0 Heq]].
    destruct (Z.eq_dec k 0).
    + subst. simpl in Heq. discriminate.
    + assert (k >= 1) by lia.
      assert (23 ^ 1 <= 23 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H0.
      lia.
Qed.