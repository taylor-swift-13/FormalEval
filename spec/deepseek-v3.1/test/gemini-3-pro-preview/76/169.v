Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 2188 16777217 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hge Heq]].
    assert (k = 0 \/ k >= 1) as [Hk0 | Hk1] by lia.
    + subst k. simpl in Heq. discriminate Heq.
    + assert (16777217 ^ 1 <= 16777217 ^ k) as Hmono.
      { apply Z.pow_le_mono_r; lia. }
      rewrite Heq in Hmono.
      simpl in Hmono.
      lia.
Qed.