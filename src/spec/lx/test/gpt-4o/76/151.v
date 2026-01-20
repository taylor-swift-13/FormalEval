Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 242 242 true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _.
    exists 1. simpl. reflexivity.
  - intros [k Hk].
    subst.
    reflexivity.
Qed.