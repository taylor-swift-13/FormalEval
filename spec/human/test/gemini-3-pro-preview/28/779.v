Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["a"; "ab"; "abc"; "abcd"; "🦌"; "abcde"; "abc8789d"; "abcdef"; "abcd"] "aababcabcd🦌abcdeabc8789dabcdefabcd".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.