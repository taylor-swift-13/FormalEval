Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 23 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge Hpow]].
    assert (k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H as [H0 | [H1 | H2]].
    + subst. simpl in Hpow. lia.
    + subst. simpl in Hpow. lia.
    + assert (5^2 <= 5^k).
      { apply Z.pow_le_mono_r; lia. }
      lia.
Qed.