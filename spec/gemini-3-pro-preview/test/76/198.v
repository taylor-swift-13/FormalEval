Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 65537 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - discriminate.
  - intros [k [Hge Heq]].
    assert (k < 7 \/ k >= 7) by lia.
    destruct H as [Hlt | Hge7].
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
      destruct H as [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]]; simpl in Heq; lia.
    + assert (6 ^ 7 <= 6 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      rewrite <- Heq in H.
      lia.
Qed.