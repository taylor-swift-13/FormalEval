Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 35 49 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Hpow]].
    destruct (Z.eq_dec k 0) as [Heq | Hneq].
    + subst k. simpl in Hpow. lia.
    + assert (Hge: 49 ^ 1 <= 49 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hge. rewrite <- Hpow in Hge. lia.
Qed.