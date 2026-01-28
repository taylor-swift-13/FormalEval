Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 82 7 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k < 3 \/ k >= 3) by lia.
    destruct H as [Hlt | Hge].
    + assert (k = 0 \/ k = 1 \/ k = 2) by lia.
      destruct H as [? | [? | ?]]; subst k; simpl in Heq; discriminate.
    + assert (7 ^ 3 <= 7 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      rewrite Heq in H.
      lia.
Qed.