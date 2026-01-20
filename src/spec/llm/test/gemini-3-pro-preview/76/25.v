Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 21 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (H_cases: k < 5 \/ k >= 5) by lia.
    destruct H_cases as [Hlt | Hge].
    + assert (H_small: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
      destruct H_small as [? | [? | [? | [? | ?]]]]; subst k; simpl in Heq; lia.
    + assert (H_pow: 2 ^ 5 <= 2 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Heq in H_pow.
      simpl in H_pow.
      lia.
Qed.