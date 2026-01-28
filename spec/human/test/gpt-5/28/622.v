Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["that"%string; "a"%string; "ab"%string; "abc"%string; "abcd"%string; "abcde"%string; "abcdef"%string; "abc"%string; "a"%string] ("thataababcabcdabcdeabcdefabca"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.