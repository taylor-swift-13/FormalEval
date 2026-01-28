Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 81 25 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k [Hpos Heq]].
    assert (Hcases: k = 0 \/ k = 1 \/ k >= 2) by lia.
    destruct Hcases as [H0 | [H1 | H2]].
    + subst k. simpl in Heq. lia.
    + subst k. simpl in Heq. lia.
    + assert (Hmono: 25 ^ 2 <= 25 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Heq in Hmono.
      simpl in Hmono.
      lia.
Qed.