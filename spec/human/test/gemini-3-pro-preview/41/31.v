Require Import Arith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example test_problem_41 : problem_41_spec 45 2025.
Proof.
  (* Unfold the definition of the specification *)
  unfold problem_41_spec.
  
  (* Simplify the multiplication: 45 * 45 evaluates to 2025 *)
  simpl.
  
  (* Prove that 2025 equals 2025 *)
  reflexivity.
Qed.