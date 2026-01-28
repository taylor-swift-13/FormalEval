Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 4 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk Hpow]].
    destruct (Z.eq_dec k 0) as [Heq | Hneq].
    + subst.
      simpl in Hpow.
      discriminate.
    + assert (1 <= k) by lia.
      assert (5 ^ 1 <= 5 ^ k).
      {
        apply Z.pow_le_mono_r; lia.
      }
      simpl in H.
      lia.
Qed.