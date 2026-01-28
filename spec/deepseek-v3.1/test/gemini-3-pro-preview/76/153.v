Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 16777217 16777216 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hge Heq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [Hk | [Hk | Hk]] by lia.
    + subst. simpl in Heq. discriminate Heq.
    + subst. simpl in Heq. discriminate Heq.
    + assert (H : 16777216 ^ 2 <= 16777216 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Heq in H.
      assert (Hcontra : 16777216 ^ 2 > 16777217) by (vm_compute; reflexivity).
      lia.
Qed.