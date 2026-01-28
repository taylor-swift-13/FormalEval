Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 4722366482869645213696 1099511627776 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hk Heq]].
    assert (k < 2 \/ k >= 2) as [Hlt | Hge] by lia.
    + assert (k = 0 \/ k = 1) as [-> | ->] by lia; simpl in Heq; discriminate.
    + assert (Hmono: 1099511627776 ^ 2 <= 1099511627776 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite <- Heq in Hmono.
      assert (Hcalc: 1099511627776 ^ 2 > 4722366482869645213696) by (vm_compute; reflexivity).
      lia.
Qed.