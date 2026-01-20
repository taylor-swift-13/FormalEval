Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 26 0 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. exfalso. discriminate.
  - intros [k Hk]. exfalso.
    assert (Hn: 26 = 0 ^ k) by assumption.
    destruct k; simpl in Hn; inversion Hn.
Qed.