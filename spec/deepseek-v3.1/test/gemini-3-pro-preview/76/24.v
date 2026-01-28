Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 23 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    inversion H.
  - intros [k [Hk_ge_0 H_pow]].
    assert (k < 5 \/ k >= 5) by lia.
    destruct H as [H_lt_5 | H_ge_5].
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
      destruct H as [? | [? | [? | [? | ?]]]]; subst; simpl in H_pow; lia.
    + assert (2 ^ 5 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      lia.
Qed.