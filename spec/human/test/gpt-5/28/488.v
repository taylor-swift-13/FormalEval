Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["this\nstring\nhas\nmultiple\nnewlines"%string; "jumps"%string; "jumps"%string; "jums"%string; "jums"%string; "this\nstring\nhas\nmultiple\nnewlines"%string] ("this\nstring\nhas\nmultiple\nnewlinesjumpsjumpsjumsjumsthis\nstring\nhas\nmultiple\nnewlines"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.