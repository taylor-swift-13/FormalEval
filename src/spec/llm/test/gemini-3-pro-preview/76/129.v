Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 16777216 16777217 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k >= 1) as [H0 | H1] by lia.
    + subst k. simpl in Heq. lia.
    + assert (16777217 ^ 1 <= 16777217 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      lia.
Qed.