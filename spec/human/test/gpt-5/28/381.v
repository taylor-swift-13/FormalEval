Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["The"%string; "quick"%string; "woood"%string; "brown"%string; "Hellsingleo, World!"%string; "jumps"%string; "fox"%string; "11"%string; "extra"%string; "the"%string; "or"%string; "lazy"%string; "over"%string] ("ThequickwooodbrownHellsingleo, World!jumpsfox11extratheorlazyover"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.