Require Import Arith.

Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example problem_41_test_case : 
  problem_41_spec 1002 1004004.
Proof.
  simpl.
  unfold problem_41_spec.
  (* We prove 1004004 = 1002 * 1002 by arithmetic reasoning *)

  (* Compute 1002 * 1002 using the fact that (a + b)^2 = a^2 + 2ab + b^2 *)
  (* Here, 1002 = 1000 + 2 *)
  assert (H: 1002 * 1002 = 1000 * 1000 + 2 * 1000 * 2 + 2 * 2).
  {
    rewrite <- Nat.mul_add_distr_l.
    rewrite <- Nat.mul_add_distr_l.
    ring.
  }
  rewrite H.
  simpl.
  reflexivity.
Qed.