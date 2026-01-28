Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 16777215 16777216 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H0 | [H1 | H2]] by lia.
    + subst. simpl in Heq. discriminate.
    + subst. simpl in Heq. discriminate.
    + assert (16777216 ^ 1 < 16777216 ^ k) as Hlt.
      { apply Z.pow_lt_mono_r; lia. }
      rewrite <- Heq in Hlt.
      rewrite Z.pow_1_r in Hlt.
      lia.
Qed.