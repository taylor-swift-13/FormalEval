Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 4722366482869645213695 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    destruct (Z.eq_dec k 0) as [Hk0 | Hk_neq_0].
    + subst k. simpl in Hk_eq.
      vm_compute in Hk_eq. discriminate.
    + assert (Hk_pos : 0 <= k - 1) by lia.
      replace k with (Z.succ (k - 1)) in Hk_eq by lia.
      rewrite Z.pow_succ_r in Hk_eq; [| assumption].
      apply (f_equal Z.odd) in Hk_eq.
      rewrite Z.odd_mul in Hk_eq.
      replace (Z.odd 4) with false in Hk_eq by reflexivity.
      simpl in Hk_eq.
      vm_compute in Hk_eq.
      discriminate.
Qed.