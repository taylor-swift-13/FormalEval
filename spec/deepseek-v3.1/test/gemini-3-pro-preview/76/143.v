Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 246 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge0 Heq]].
    assert (Hcases: k < 4 \/ k >= 4) by lia.
    destruct Hcases as [Hsmall | Hlarge].
    + assert (Hk: k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct Hk as [E | [E | [E | E]]]; rewrite E in Heq; simpl in Heq; lia.
    + assert (Hpow: 5 ^ 4 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      rewrite Heq in Hpow.
      lia.
Qed.