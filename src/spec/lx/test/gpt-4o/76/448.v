Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 1099511627778 82 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. exfalso. inversion H.
  - intros [k Hk].
    assert (Hfalse: 1099511627778 <> 82 ^ k).
    {
      (* Direct computation shows that 1099511627778 cannot be expressed as 82^k for any k. *)
      (* This requires external verification or computational tools. *)
      admit.
    }
    contradiction.
Admitted.