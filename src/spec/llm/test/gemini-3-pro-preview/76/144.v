Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 242 1099511627776 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk_ge_0 Hk_eq]].
    assert (H_cases: k = 0 \/ k >= 1) by lia.
    destruct H_cases as [Hk0 | Hk1].
    + subst k. simpl in Hk_eq. discriminate.
    + assert (H_ineq: 1099511627776 ^ 1 <= 1099511627776 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_ineq.
      lia.
Qed.