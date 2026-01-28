Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 24 10 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H | [H | H]] by lia.
    + subst. simpl in Hk2. discriminate.
    + subst. simpl in Hk2. discriminate.
    + assert (100 <= 10 ^ k).
      { change 100 with (10 ^ 2). apply Z.pow_le_mono_r; lia. }
      lia.
Qed.