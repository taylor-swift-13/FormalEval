Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 3 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H as [Hk0 | [Hk1 | Hk2]].
    + subst k.
      simpl in Hk_eq.
      lia.
    + subst k.
      simpl in Hk_eq.
      lia.
    + assert (5 ^ 2 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      lia.
Qed.