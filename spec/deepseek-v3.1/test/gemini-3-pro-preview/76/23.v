Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 25 23 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hnonneg Heq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H0 | [H1 | H2]] by lia.
    + subst k. simpl in Heq. discriminate.
    + subst k. simpl in Heq. discriminate.
    + assert (23 ^ 2 <= 23 ^ k) as Hle.
      { apply Z.pow_le_mono_r; lia. }
      rewrite Heq in Hle.
      simpl in Hle.
      lia.
Qed.