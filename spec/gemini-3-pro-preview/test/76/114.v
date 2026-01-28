Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 245 27 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H0 | [H1 | H2]] by lia.
    + subst. simpl in Heq. discriminate.
    + subst. simpl in Heq. discriminate.
    + assert (27 ^ 2 <= 27 ^ k) by (apply Z.pow_le_mono_r; lia).
      rewrite <- Heq in H.
      change (27 ^ 2) with 729 in H.
      lia.
Qed.