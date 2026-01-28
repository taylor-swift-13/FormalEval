Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 65537 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk1 Hk2]].
    assert (k < 7 \/ k >= 7) as [Hlt | Hge] by lia.
    + assert (Hsmall: k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
      destruct Hsmall as [ | [ | [ | [ | [ | [ | ]]]]]]; subst; simpl in Hk2; discriminate.
    + assert (Hpow: 5 ^ 7 <= 5 ^ k) by (apply Z.pow_le_mono_r; lia).
      simpl in Hpow.
      lia.
Qed.