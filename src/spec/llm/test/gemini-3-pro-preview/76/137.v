Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 81 16777217 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - discriminate.
  - intros [k [Hk Hx]].
    assert (k = 0 \/ k > 0) as [H0 | Hpos] by lia.
    + subst k. simpl in Hx. discriminate.
    + assert (16777217 ^ 1 <= 16777217 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Hx in H.
      simpl in H.
      lia.
Qed.