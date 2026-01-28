Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 82 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hpos Hpow]].
    assert (Hcases: k < 5 \/ k >= 5) by lia.
    destruct Hcases as [Hlt | Hge].
    + assert (Hvals: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
      destruct Hvals as [? | [? | [? | [? | ?]]]]; subst k; simpl in Hpow; lia.
    + assert (Hmono: 3 ^ 5 <= 3 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hmono.
      rewrite Hpow in Hmono.
      lia.
Qed.