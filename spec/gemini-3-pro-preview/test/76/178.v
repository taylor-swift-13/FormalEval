Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 4722366482869645213696 4722366482869645213695 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hk Heq]].
    assert (Hk_cases: k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct Hk_cases as [H0 | [H1 | H2]].
    + subst k. vm_compute in Heq. discriminate.
    + subst k. rewrite Z.pow_1_r in Heq. vm_compute in Heq. discriminate.
    + assert (Hle: 4722366482869645213695 ^ 2 <= 4722366482869645213695 ^ k).
      { apply Z.pow_le_mono_r; try lia. }
      assert (Hlt: 4722366482869645213696 < 4722366482869645213695 ^ 2).
      { vm_compute. reflexivity. }
      rewrite Heq in Hlt.
      lia.
Qed.