Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["lHello, W,orld!"%string; "Hello, World!"%string; "Hello, W,orld!"%string] ("lHello, W,orld!Hello, World!Hello, W,orld!"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.