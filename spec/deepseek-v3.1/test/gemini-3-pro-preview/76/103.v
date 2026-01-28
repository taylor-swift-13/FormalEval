Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 49 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge Hpow]].
    assert (k < 4 \/ k >= 4) by lia.
    destruct H as [Hsmall | Hlarge].
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct H as [H0 | [H1 | [H2 | H3]]]; subst; simpl in Hpow; discriminate.
    + assert (3 ^ 4 <= 3 ^ k) by (apply Z.pow_le_mono_r; lia).
      simpl in H.
      lia.
Qed.