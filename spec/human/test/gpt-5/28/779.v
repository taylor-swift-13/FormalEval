Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["a"%string; "ab"%string; "abc"%string; "abcd"%string; "🦌"%string; "abcde"%string; "abc8789d"%string; "abcdef"%string; "abcd"%string] ("aababcabcd🦌abcdeabc8789dabcdefabcd"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.