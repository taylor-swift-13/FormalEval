Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 143214 16 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    inversion H.
  - intros [k [Hk1 Hk2]].
    assert (k < 5 \/ k >= 5) as [Hlt | Hge] by lia.
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) as Hcases by lia.
      destruct Hcases as [H | [H | [H | [H | H]]]]; subst k; simpl in Hk2; lia.
    + assert (16 ^ 5 <= 16 ^ k) as Hpow.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hpow.
      rewrite Hk2 in Hpow.
      lia.
Qed.