Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 16777216 1 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate.
  - intros [k Hk].
    assert (H1: 16777216 = 1 ^ k) by assumption.
    rewrite Nat.pow_1_l in H1.
    discriminate.
Qed.