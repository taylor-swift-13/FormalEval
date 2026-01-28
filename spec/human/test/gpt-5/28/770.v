Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["a"%string; "ab18characters"%string; "ab"%string; "abcd"%string; "🦌"%string; "🐯"%string; "abcde"%string; "achara1longctersbc8789d"%string; "abcdef"%string] ("aab18charactersababcd🦌🐯abcdeachara1longctersbc8789dabcdef"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.