Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 8190 4722366482869645213695 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    exfalso.
    unfold not in H.
    destruct H as [k Hk].
    (* Here, we show that no such k exists such that 8190 = 4722366482869645213695 ^ k. *)