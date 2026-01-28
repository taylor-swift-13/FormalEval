Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 24 2 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate H.
  - intros [k [Hk_ge_0 Hk_pow]].
    assert (k < 5 \/ k >= 5) as [Hk_lt | Hk_ge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) as Hk_cases by lia.
      destruct Hk_cases as [Hk | [Hk | [Hk | [Hk | Hk]]]]; subst k; simpl in Hk_pow; discriminate Hk_pow.
    + assert (2 ^ 5 <= 2 ^ k) as H_mono.
      { apply Z.pow_le_mono_r; lia. }
      simpl in H_mono.
      lia.
Qed.