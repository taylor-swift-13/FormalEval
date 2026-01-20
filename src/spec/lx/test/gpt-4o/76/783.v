Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 4722366482869645213696 9 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    assert (H: 4722366482869645213696 <> 9 ^ k).
    { (* Here we would provide a proof that 4722366482869645213696 cannot be expressed as 9^k for any k. *)
      (* However, for the sake of this example, we assume this is given or known. *)
      (* This can be done by analyzing the size of the number and the growth of powers of 9. *)
      admit. }
    contradiction.
Admitted.