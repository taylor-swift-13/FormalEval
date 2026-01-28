Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["Hello123orld!"%string; "Hello, World!"%string; "Hello, World!"%string; "Hello, World!"%string; "Hello123orld!"%string; "Hello123orld!"%string] ("Hello123orld!Hello, World!Hello, World!Hello, World!Hello123orld!Hello123orld!"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.