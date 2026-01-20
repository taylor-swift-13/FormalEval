Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 16777217 243 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    assert (Hfalse: 16777217 <> 243 ^ k).
    { (* Proof by contradiction *)
      (* Placeholder for reasoning that 16777217 cannot be expressed as 243^k for any k *)
      (* This assertion is necessary to establish the falsity. *)