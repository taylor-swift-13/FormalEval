Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  ["hello\nworld"%string;
   "this\nstring\nhas\nmultiple\nnewlines"%string;
   "1or"%string;
   "jumps"%string;
   "hello\nw14orld"%string;
   "hello\nworld"%string;
   "hello\nworld"%string;
   "hello\nworld"%string]
  ("hello\nworldthis\nstring\nhas\nmultiple\nnewlines1orjumpshello\nw14orldhello\nworldhello\nworldhello\nworld"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.