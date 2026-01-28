Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 243 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge Hk]].
    assert (k < 3 \/ k = 3 \/ k >= 4) by lia.
    destruct H as [Hlt | [Heq | Hgt]].
    + assert (k = 0 \/ k = 1 \/ k = 2) by lia.
      destruct H as [? | [? | ?]]; subst; simpl in Hk; lia.
    + subst. simpl in Hk. lia.
    + assert (6 ^ 4 <= 6 ^ k)%Z.
      { apply Z.pow_le_mono_r; lia. }
      simpl in H. rewrite Hk in H. lia.
Qed.