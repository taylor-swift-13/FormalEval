Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 15 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [Hge Heq]].
    assert (k < 3 \/ k >= 3) by lia.
    destruct H as [Hlt | Hge3].
    + assert (k = 0 \/ k = 1 \/ k = 2) by lia.
      destruct H as [H0 | [H1 | H2]]; subst; simpl in Heq; lia.
    + assert (3 ^ 3 <= 3 ^ k) by (apply Z.pow_le_mono_r; lia).
      simpl in H. lia.
Qed.