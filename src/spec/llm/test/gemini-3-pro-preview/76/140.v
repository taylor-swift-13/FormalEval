Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 242 16777216 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k >= 1) by lia.
    destruct H as [-> | Hge].
    + simpl in Heq. discriminate.
    + assert (16777216 <= 16777216 ^ k).
      { change 16777216 with (16777216 ^ 1).
        apply Z.pow_le_mono_r; lia. }
      lia.
Qed.