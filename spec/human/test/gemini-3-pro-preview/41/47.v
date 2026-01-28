Require Import ZArith.
Open Scope Z_scope.

(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : Z) : Prop := True.

Definition problem_41_spec(input output : Z) : Prop :=
  output = input * input.

Example test_problem_41 : problem_41_spec 987653 975458448409.
Proof.
  (* Unfold the definition of the specification *)
  unfold problem_41_spec.
  
  (* Simplify the multiplication: 987653 * 987653 evaluates to 975458448409 *)
  simpl.
  
  (* Prove that 975458448409 equals 975458448409 *)
  reflexivity.
Qed.