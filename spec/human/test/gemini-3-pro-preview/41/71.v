Require Import Arith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example test_problem_41 : problem_41_spec 56 3136.
Proof.
  (* Unfold the definition of the specification *)
  unfold problem_41_spec.
  
  (* Simplify the multiplication: 56 * 56 evaluates to 3136 *)
  simpl.
  
  (* Prove that 3136 equals 3136 *)
  reflexivity.
Qed.