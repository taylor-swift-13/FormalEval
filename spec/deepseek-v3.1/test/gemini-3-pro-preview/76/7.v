Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 128 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hpos Heq]].
    destruct (Z_lt_ge_dec k 4).
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
      destruct H as [-> | [-> | [-> | ->]]]; simpl in Heq; lia.
    + assert (4 ^ 4 <= 4 ^ k)%Z.
      { apply Z.pow_le_mono_r; lia. }
      rewrite Heq in H.
      simpl in H.
      lia.
Qed.