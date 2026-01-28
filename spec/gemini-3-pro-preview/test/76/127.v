Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 245 244 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hk Heq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H0 | [H1 | H2]] by lia.
    + subst k. simpl in Heq. lia.
    + subst k. simpl in Heq. lia.
    + assert (244 ^ 2 <= 244 ^ k) as Hle by (apply Z.pow_le_mono_r; lia).
      replace (244 ^ 2) with 59536 in Hle by reflexivity.
      lia.
Qed.