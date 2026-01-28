Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 36 5 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k [H1 H2]].
    assert (k = 0 \/ k = 1 \/ k = 2 \/ k >= 3) by lia.
    destruct H as [H | [H | [H | H]]].
    + subst. simpl in H2. discriminate.
    + subst. simpl in H2. discriminate.
    + subst. simpl in H2. discriminate.
    + assert (5^3 <= 5^k) by (apply Z.pow_le_mono_r; lia).
      simpl in H0.
      rewrite H2 in H0.
      lia.
Qed.