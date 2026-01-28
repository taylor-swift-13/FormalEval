Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 4722366482869645213696 1099511627777 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k = 0 \/ k = 1 \/ k >= 2) as [H0 | [H1 | H2]] by lia.
    + subst k. simpl in Hk2. vm_compute in Hk2. discriminate.
    + subst k. rewrite Z.pow_1_r in Hk2. vm_compute in Hk2. discriminate.
    + assert (1099511627777 ^ 2 <= 1099511627777 ^ k) as Hle.
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk2 in Hle.
      assert (4722366482869645213696 < 1099511627777 ^ 2) as Hlt.
      { vm_compute. reflexivity. }
      lia.
Qed.