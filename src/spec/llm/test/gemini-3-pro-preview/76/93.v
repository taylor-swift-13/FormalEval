Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 65 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - discriminate.
  - intros [k [Hk1 Hk2]].
    assert (Hdec : k < 3 \/ k >= 3) by lia.
    destruct Hdec as [Hlt | Hge].
    + assert (Hcases : k = 0 \/ k = 1 \/ k = 2) by lia.
      destruct Hcases as [-> | [-> | ->]]; simpl in Hk2; discriminate.
    + assert (Hmono : 5 ^ 3 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hmono.
      rewrite <- Hk2 in Hmono.
      lia.
Qed.