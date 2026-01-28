Require Import Arith.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Example test_problem_41 : problem_41_spec 23 529.
Proof.
  (* Unfold the definition of the specification *)
  unfold problem_41_spec.
  
  (* Simplify the multiplication: 23 * 23 evaluates to 529 *)
  simpl.
  
  (* Prove that 529 equals 529 *)
  reflexivity.
Qed.