Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["Hello123orld!"; "Hello, World!"; "Hello, World!"; "Hello, World!"; "Hello123orld!"; "Hello123orld!"] "Hello123orld!Hello, World!Hello, World!Hello, World!Hello123orld!Hello123orld!".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.