Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 4 1 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    simpl in Hk. subst.
    assert (H: 1 ^ k = 1) by apply Nat.pow_1_l.
    rewrite H in Hk.
    discriminate Hk.
Qed.