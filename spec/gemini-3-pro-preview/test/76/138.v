Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 243 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Hpow]].
    assert (k < 4 \/ k >= 4) by lia.
    destruct H as [Hlt | Hge].
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct H as [? | [? | [? | ?]]]; subst; simpl in Hpow; discriminate.
    + assert (4 ^ 4 <= 4 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      replace (4 ^ 4) with 256 in H by reflexivity.
      lia.
Qed.