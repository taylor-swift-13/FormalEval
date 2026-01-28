Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 6 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hge Heq]].
    assert (k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct H as [H | [H | H]].
    + subst. simpl in Heq. discriminate.
    + subst. simpl in Heq. discriminate.
    + assert (5 ^ 2 <= 5 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H0.
      lia.
Qed.