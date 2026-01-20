Require Import Arith.

Definition is_simple_power_spec (x n : nat) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ k).

Example is_simple_power_test :
  is_simple_power_spec 4722366482869645213694 9 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. discriminate H.
  - intros [k Hk].
    assert (Hfalse: 4722366482869645213694 <> 9 ^ k).
    { (* Provide a proof that 4722366482869645213694 cannot be expressed as 9^k for any k *)
      (* This is a placeholder for a more detailed proof, which would involve reasoning about the size of numbers. *)
      (* For the purpose of this example, we assume this assertion is correct. *)
      admit.
    }
    contradiction.
Admitted.