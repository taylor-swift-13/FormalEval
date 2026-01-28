Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 5 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H0 | [H1 | H2]] by lia.
    + subst k. simpl in Heq. discriminate Heq.
    + subst k. simpl in Heq. discriminate Heq.
    + assert (4 ^ 2 <= 4 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      rewrite Heq in H.
      lia.
Qed.