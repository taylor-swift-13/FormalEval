Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (res : bool) : Prop :=
  res = true <-> exists k : Z, 0 <= k /\ x = n ^ k.

Example test_is_simple_power : is_simple_power_spec 143214 16 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hk Hx]].
    assert (k < 5 \/ k >= 5) by lia.
    destruct H as [Hsmall | Hlarge].
    + assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
      destruct H as [? | [? | [? | [? | ?]]]]; subst; simpl in Hx; lia.
    + assert (16 ^ 5 <= 16 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      lia.
Qed.