Require Import Arith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example test_problem_41 : problem_41_spec 58 3364.
Proof.
  (* Unfold the definition of the specification *)
  unfold problem_41_spec.
  
  (* Simplify the multiplication: 58 * 58 evaluates to 3364 *)
  simpl.
  
  (* Prove that 3364 equals 3364 *)
  reflexivity.
Qed.